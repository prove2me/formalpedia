-- Prove2me | solution 1 for SpherePacking.trace_sq_le_finiteHilbertSchmidtKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/95ad2119-366e-4fc5-a87a-36a53d13b731

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) :
    (T.trace ℝ E) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        finiteHilbertSchmidtKernel b (fun _ : Unit => T) () () := by
  classical
  rw [LinearMap.trace_eq_sum_inner T b]
  unfold finiteHilbertSchmidtKernel
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset ι)
      (fun _ : ι => (1 : ℝ))
      (fun i : ι => ⟪b i, T (b i)⟫_ℝ)
  calc
    (∑ i : ι, ⟪b i, T (b i)⟫_ℝ) ^ 2 ≤
        (Fintype.card ι : ℝ) *
          ∑ i : ι, ⟪b i, T (b i)⟫_ℝ ^ 2 := by
      simpa using hcs
    _ ≤ (Fintype.card ι : ℝ) *
          ∑ i : ι, ⟪T (b i), T (b i)⟫_ℝ := by
      apply mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
      have hi := real_inner_mul_inner_self_le (b i) (T (b i))
      simpa [pow_two] using hi
end SpherePacking
