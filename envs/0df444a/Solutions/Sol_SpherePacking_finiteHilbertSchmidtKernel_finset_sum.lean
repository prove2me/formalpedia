-- Prove2me | solution 1 for SpherePacking.finiteHilbertSchmidtKernel_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/d0e206e0-102a-4f2d-8245-43d348f1fb3c

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
    {α ι F E : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ F)
    (C : Finset α) (A : α → F →ₗ[ℝ] E) :
    finiteHilbertSchmidtKernel b
      (fun _ : Unit => ∑ x ∈ C, A x) () () =
      ∑ x ∈ C, ∑ y ∈ C, finiteHilbertSchmidtKernel b A x y := by
  classical
  unfold finiteHilbertSchmidtKernel
  simp_rw [LinearMap.sum_apply, sum_inner, inner_sum]
  calc
    (∑ i : ι, ∑ x ∈ C, ∑ y ∈ C,
      ⟪A x (b i), A y (b i)⟫_ℝ) =
        ∑ x ∈ C, ∑ i : ι, ∑ y ∈ C,
          ⟪A x (b i), A y (b i)⟫_ℝ := by
            rw [Finset.sum_comm]
    _ = ∑ x ∈ C, ∑ y ∈ C, ∑ i : ι,
          ⟪A x (b i), A y (b i)⟫_ℝ := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_comm]
end SpherePacking
