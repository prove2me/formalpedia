-- Prove2me | solution 1 for SpherePacking.isometric_projection_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/b95d68dd-8256-4b73-95de-f4ecee22c48e

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
    {F E : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (f : F →ₗᵢ[ℝ] E) :
    ((f.toLinearMap ∘ₗ f.adjoint).trace ℝ E) =
      (Module.finrank ℝ F : ℝ) := by
  calc
    ((f.toLinearMap ∘ₗ f.adjoint).trace ℝ E) =
        ((f.adjoint ∘ₗ f.toLinearMap).trace ℝ F) :=
      (LinearMap.trace_comp_comm' f.toLinearMap f.adjoint).symm
    _ = (LinearMap.id.trace ℝ F) := by
      rw [f.adjoint_comp_self']
    _ = (Module.finrank ℝ F : ℝ) :=
      LinearMap.trace_id ℝ F
end SpherePacking
