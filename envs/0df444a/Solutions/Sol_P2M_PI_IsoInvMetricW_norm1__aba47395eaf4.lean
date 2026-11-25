-- Prove2me | solution 1 for P2M_PI_IsoInvMetricW_norm1__aba47395eaf4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:43.379964+00:00
-- url     : https://prove2.me/submissions/be86123b-675d-4c66-b73d-88558b67e85d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Theorems.Thm_PI_IsoInvMetricW_unitVector_val_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
namespace PI.IsoInvMetricW
theorem _root_.solution : Norm1 := by
  intro Lt _ _ N nu hle
  unfold l2
  rw [finsum_eq_sum_of_fintype]
  simp [unitVector_val_eq nu hle, apply_ite (fun x : ℂ => ‖x‖ ^ 2)]
end PI.IsoInvMetricW
