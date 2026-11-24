-- Prove2me | solution 1 for PI.ScRefExists.WB.hG_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:58:51.304809+00:00
-- url     : https://prove2.me/submissions/e55c0b3a-41af-4514-8509-79e4c8402cd9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGZeroRight
import Theorems.Thm_PI_ScRefExists_WB_hG_def
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WB
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.WB
theorem _root_.solution (x : Fin I.n → I.E) : hG I x 0 = 0 := by simp [hG_def]
end PI.ScRefExists.WB
