-- Prove2me | solution 1 for Transcendence.partials_eq_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T10:37:18.797115+00:00
-- url     : https://prove2.me/submissions/5dad7d7c-f3d2-4345-9aa2-84eae993b25b

import Mathlib

/-!
# Coordinate partial derivatives are values of `iteratedFDeriv`

For `g : (ι → 𝕜) → F`, the partial derivative in coordinate `i` at `z` is the derivative of the
slice `w ↦ g (update z i w)` at `z i`. Iterating it along `L 0, …, L (k-1)` (the last one first)
gives `iteratedFDeriv 𝕜 k g z` on the coordinate vectors `Pi.single (L l) 1`, by induction on `k`:
the inner `k - 1` partials are `iteratedFDeriv` by induction, a differentiable function of `z`, and
its slice derivative is `fderiv` in the direction `Pi.single (L 0) 1`
(`iteratedFDeriv_succ_apply_left`).
-/

namespace PartialsEqIteratedFDeriv

open Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of the slice in coordinate `i` is `fderiv` in the direction `Pi.single i 1`. -/
lemma deriv_slice {g : (ι → 𝕜) → F} (hg : Differentiable 𝕜 g) (i : ι) (z : ι → 𝕜) :
    deriv (fun w => g (update z i w)) (z i) = fderiv 𝕜 g z (Pi.single i 1) := by
  have h := (hg (update z i (z i))).hasFDerivAt.comp_hasDerivAt (z i)
    (hasDerivAt_update z i (z i))
  rw [update_eq_self] at h
  exact h.deriv

end PartialsEqIteratedFDeriv

open PartialsEqIteratedFDeriv in
/-- **Coordinate partial derivatives are values of `iteratedFDeriv`.** -/
theorem solution {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {k : ℕ} (L : Fin k → ι) {g : (ι → 𝕜) → F} (hg : ContDiff 𝕜 k g) (z : ι → 𝕜) :
    (List.ofFn L).foldr (fun i h y => deriv (fun w => h (Function.update y i w)) (y i)) g z =
      iteratedFDeriv 𝕜 k g z (fun l => Pi.single (L l) 1) := by
  induction k generalizing g z with
  | zero => simp
  | succ k ih =>
    have hd : Differentiable 𝕜 (iteratedFDeriv 𝕜 k g) :=
      hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
    have e := funext fun y => ih (fun l => L l.succ) (hg.of_le (by exact_mod_cast Nat.le_succ k)) y
    simp only [List.ofFn_succ, List.foldr_cons]
    rw [e, deriv_slice (hd.continuousMultilinear_apply_const _),
      fderiv_continuousMultilinear_apply_const_apply (hd z), iteratedFDeriv_succ_apply_left]
    rfl
