-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.f_Pw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:00.913903+00:00
-- url     : https://prove2.me/submissions/00345da8-da16-4daa-915d-1fa088ce9154

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_sub
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_f_sum_e
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_f_sum_f
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
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (b : Fin r) (v : Fin n → ℂ) : hJ ε (f b) (Pw ε e f v) = 0 := by
  unfold Pw
  simp only [hJ_sub, f_sum_e hG, f_sum_f hG, sub_self, sub_zero]
end PI.NMeasInv.UnitaryGroupMassFormula
