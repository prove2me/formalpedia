-- Prove2me | solution 1 for SpherePacking.finiteHilbertSchmidtKernel_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/09ff98c9-944e-4dd4-80eb-65f0cddf738d

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
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ F)
    (A : α → F →ₗ[ℝ] E) (x y : α) :
    finiteHilbertSchmidtKernel b A x y =
      ((A x).adjoint ∘ₗ A y).trace ℝ F := by
  unfold finiteHilbertSchmidtKernel
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
end SpherePacking
