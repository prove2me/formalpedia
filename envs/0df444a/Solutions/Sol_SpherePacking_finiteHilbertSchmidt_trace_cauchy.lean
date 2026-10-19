-- Prove2me | solution 1 for SpherePacking.finiteHilbertSchmidt_trace_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/602c2ff2-7713-4407-bd99-2c1b6899fd4f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_finiteHilbertSchmidtKernel_finset_sum
import Theorems.Thm_SpherePacking_trace_sq_le_finiteHilbertSchmidtKernel

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
    {α ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (C : Finset α) (A : α → E →ₗ[ℝ] E) :
    (∑ x ∈ C, (A x).trace ℝ E) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        ∑ x ∈ C, ∑ y ∈ C,
          finiteHilbertSchmidtKernel b A x y := by
  have h := trace_sq_le_finiteHilbertSchmidtKernel b (∑ x ∈ C, A x)
  rw [map_sum, finiteHilbertSchmidtKernel_finset_sum b C A] at h
  exact h
end SpherePacking
