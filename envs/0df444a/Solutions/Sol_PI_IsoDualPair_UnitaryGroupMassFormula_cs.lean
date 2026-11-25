-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:36.116554+00:00
-- url     : https://prove2.me/submissions/225ecdc6-5975-4dd9-8ff2-39f5bef7ef68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_symmetricMeasure_l2Norm_eq_resolutionL2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.IsoDualPair PI.IsoDualPair.UnitaryGroupMassFormula
open PI.IsoDualPair
variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoDualPair.UnitaryGroupMassFormula
theorem _root_.solution (φ ψ : LaC N nu) : ‖prC φ ψ‖ ^ 2 ≤ l2 φ * l2 ψ := by
  rw [prC_eq, symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2]
  calc ‖∑ J, φ J * ψ J‖ ^ 2 ≤ (∑ J, ‖φ J‖ * ‖ψ J‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => norm_mul_le _ _)
    _ ≤ (∑ J, ‖φ J‖ ^ 2) * ∑ J, ‖ψ J‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
end PI.IsoDualPair.UnitaryGroupMassFormula
