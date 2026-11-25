-- Prove2me | solution 1 for PI.FJMD.shapeVector_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:35.474798+00:00
-- url     : https://prove2.me/submissions/d91a14bd-5a65-42f6-b8cb-b352f6fa12c3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Theorems.Thm_PI_FJMD_shapeProd_varMat_ne_zero
import Theorems.Thm_PI_FJMD_posPart_length
import Theorems.Thm_PI_FJMD_negPart_length

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM
namespace PI.FJMD
theorem _root_.solution : VecNe := by
  intro p q r s a b c d h
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := h
  unfold PI.FJM.hwVec
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Sum.inl_injective hxy) (by intro x y hxy; exact Sum.inl_injective hxy) _
      (by rw [posPart_length]; omega) (by rw [posPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Fin.rev_injective (Sum.inl_injective hxy))
      (by intro x y hxy; exact Fin.rev_injective (Sum.inr_injective hxy)) _
      (by rw [negPart_length]; omega) (by rw [negPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Sum.inr_injective hxy) (by intro x y hxy; exact Sum.inr_injective hxy) _
      (by rw [posPart_length]; omega) (by rw [posPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Fin.rev_injective (Sum.inr_injective hxy))
      (by intro x y hxy; exact Fin.rev_injective (Sum.inl_injective hxy)) _
      (by rw [negPart_length]; omega) (by rw [negPart_length]; omega)
end PI.FJMD
