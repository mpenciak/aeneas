import Aeneas.Std.Slice
import Aeneas.Tactic.Step
import Aeneas.Do

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.UncurryBind

/-- A toy "indexed read with a setter" that returns a pair, mirroring
    `Array.index_mut_usize`. -/
def readPair (xs : List Nat) (i : Nat) : Result (Nat × (Nat → List Nat)) :=
  ok (xs.getD i 0, fun y => xs.set i y)

@[step]
theorem readPair_spec (xs : List Nat) (i : Nat) :
    readPair xs i ⦃ x y => x = xs.getD i 0 ∧ y = (fun y => xs.set i y) ⦄ := by
  unfold readPair; simp [WP.spec_ok, WP.predn]

def readSingle (xs : List Nat) (i : Nat) : Result Nat :=
  ok (xs.getD i 0)

@[step]
theorem readSingle_spec (xs : List Nat) (i : Nat) :
    readSingle xs i ⦃ x => x = xs.getD i 0 ⦄ := by
  unfold readSingle; simp [WP.spec_ok]

/-- a `do` block alternating tuple-destructuring binds with single binds.
  Before the fix to `step*`, this was causing some issues -/
def prog (xs : List Nat) : Result (List Nat × Nat) := do
  let (a, setA) ← readPair xs 0
  let b ← readSingle xs 1
  let (c, setC) ← readPair (setA b) 2
  let d ← readSingle (setC c) 3
  ok (setC c, a + b + c + d)

-- `step*` should finish this proof off in one step, the new `do` elab use of
-- `uncurry` was preventing that
example (xs : List Nat) :
    prog xs ⦃ _ => True ⦄ := by
  unfold prog
  step*

/-! ## Step 1 regression: `Function.uncurry_apply_eq` in `step_simps`

Before adding `Function.uncurry_apply_eq` to `step_simps`, `simp only [step_simps]` on a goal
containing `Function.uncurry (fun a b => …) v` (with `v` an opaque variable) made no progress —
`Function.uncurry_apply_pair` only fires for literal pair arguments. The new lemma normalizes
`Function.uncurry f v ↦ f v.fst v.snd` regardless of `v`.
-/

example (f : Nat → Nat → Nat) (x : Nat × Nat) :
    Function.uncurry f x = f x.fst x.snd := by
  simp only [step_simps]

/-- Nested-tuple bind followed by another bind. Without `Function.uncurry_apply_eq` in
`step_simps`, after the first bind the residual program is wrapped in `Function.uncurry _ _x0`
applications that block subsequent step iterations. -/
def readNested (xs : List Nat) : Result ((Nat × Nat) × Nat) :=
  ok ((xs.getD 0 0, xs.getD 1 0), xs.getD 2 0)

@[step]
theorem readNested_spec (xs : List Nat) :
    readNested xs ⦃ r => r = ((xs.getD 0 0, xs.getD 1 0), xs.getD 2 0) ⦄ := by
  unfold readNested; simp [WP.spec_ok]

def progNested (xs : List Nat) : Result Nat := do
  let ((a, b), c) ← readNested xs
  let d ← readSingle xs 3
  ok (a + b + c + d)

example (xs : List Nat) :
    progNested xs ⦃ _ => True ⦄ := by
  unfold progNested
  step*

/-! ## Step 2 regression: `analyzeTarget` collects every binder name

`analyzeTarget` previously called `lambdaOne` on the lambda inside `Function.uncurry`,
which only kept the first binder. After `let (a, setA) ← readPair …`, the second
output was given a fresh anonymous name (`x✝`). With the array-based plumbing both
user names land in the local context. -/

-- `step*?` exposes the names step generated. Step 2 makes the second binder
-- of a tuple bind (`setA`) propagate from the source — before, it became `x`.
/--
info: Try this:

  [apply]     let* ⟨ a, setA, a_post1, a_post2 ⟩ ← readPair_spec
    let* ⟨ b, b_post ⟩ ← readSingle_spec
    agrind
-/
#guard_msgs in
example (xs : List Nat) :
    (do let (a, setA) ← readPair xs 0
        let b ← readSingle (setA a) 0
        ok (a + b)) ⦃ res => 0 ≤ res ⦄ := by
  step*?


/-! ## Step 3 regression: tuple-pattern post binders use `Function.uncurry`

Previously the `⦃ (a, b) c => … ⦄` macro emitted `predn (fun (a, b) => fun c => …)`
where `fun (a, b) => …` is a Lean pattern lambda — i.e. `match` on the (opaque)
discriminant. The match never reduced, leaving an irreducible `match` in the post.
The new macro emits `predn (Function.uncurry (fun a b => fun c => …))` which
reduces under the existing `Function.uncurry_apply_*` rewrites. -/

def mkTriple (x : Nat) : Result ((Nat × Nat) × Nat) :=
  ok ((x, x + 1), x + 2)

example (x : Nat) :
    mkTriple x ⦃ (a, b) c => a = x ∧ b = x + 1 ∧ c = x + 2 ⦄ := by
  -- Before Step 3 the post desugared to `predn (fun (a, b) => fun c => …)`,
  -- which is a Lean pattern lambda containing a `match`. `simp` could not
  -- reduce the match on an opaque scrutinee and the goal stayed open. The
  -- new macro emits `predn (Function.uncurry (fun a b => fun c => …))` which
  -- the default simp set reduces.
  simp [mkTriple]

/-! ## Step 4 regression: synthesized `_xN` binders are skipped in favour of post names

The new `do` elaborator names non-leaf tuple bind-binders `_x0`, `_x1`, …
(from `Aeneas/Do/Elab.lean::mkCurriedLambda`). These are not user-supplied
names but they are not macro-scoped either, so the previous logic kept them.
After Step 4 they are filtered out, letting the post-condition names take
precedence and giving the user-readable script. -/

def constTriple (x : Nat) : Result ((Nat × Nat) × Nat) :=
  ok ((x, x + 1), x + 2)

@[step] theorem constTriple_spec (x : Nat) :
    constTriple x ⦃ (a, b) c => a = x ∧ b = x + 1 ∧ c = x + 2 ⦄ := by
  simp [constTriple]

-- The first `let*` binder used to surface as `_x0`. After Step 4 the
-- synthesized name is filtered, and the leaf (`c`) name still wins for slot 1.
/--
info: Try this:

  [apply]     simp only [step_simps]
    let* ⟨ _, c, _, _, _ ⟩ ← constTriple_spec
    agrind
-/
#guard_msgs in
example (x : Nat) :
    (do let ((a, b), c) ← constTriple x
        ok (a + b + c)) ⦃ res => res = 3 * x + 3 ⦄ := by
  step*?

end Aeneas.Tactic.Step.Tests.UncurryBind
