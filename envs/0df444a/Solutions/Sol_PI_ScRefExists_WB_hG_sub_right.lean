-- Prove2me | solution 1 for PI.ScRefExists.WB.hG_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:47.981502+00:00
-- url     : https://prove2.me/submissions/7b9a9f6a-4a7e-463a-8d6c-9885846ce5d7

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
theorem _root_.solution (x y z : Fin I.n → I.E) : hG I x (y - z) = hG I x y - hG I x z := by
  simp only [hG_def, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end PI.ScRefExists.WB
