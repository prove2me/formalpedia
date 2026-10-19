-- Prove2me | solution 1 for SpherePacking.isometric_mixed_kernel_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/ef92ba83-ec3c-4bfb-9e82-48e03bfb889c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_finiteHilbertSchmidtKernel_eq_trace
import Theorems.Thm_SpherePacking_isometric_mixed_kernel_eq_overlap

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
open Filter
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution
    {α ι ρ F E : Type*} [Fintype ι] [Fintype ρ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (bE : OrthonormalBasis ι ℝ E)
    (bF : OrthonormalBasis ρ ℝ F)
    (f : α → F →ₗᵢ[ℝ] E) (x : α) :
    mixedHilbertSchmidtKernel bE
      (fun z => (f z).toLinearMap)
      (fun z => (f z).toLinearMap) x x =
      (Module.finrank ℝ F : ℝ) := by
  rw [isometric_mixed_kernel_eq_overlap bE bF f x x,
    finiteHilbertSchmidtKernel_eq_trace,
    (f x).adjoint_comp_self']
  simp [LinearMap.trace_id]
end SpherePacking
