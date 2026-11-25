-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.e_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:08.131997+00:00
-- url     : https://prove2.me/submissions/2882053f-98b4-40a3-845e-1a7ef432771a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_e_sum_e
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_e_sum_f
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_e_Pw
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
theorem _root_.solution (s : Fin r → ℝ) (b : Fin r) (v : Fin n → ℂ) :
    hJ ε (e b) (Afun ε e f s v) = (s b : ℂ)⁻¹ * hJ ε (e b) v := by
  unfold Afun
  simp only [hJ_add, e_sum_e hG, e_sum_f hG, e_Pw hG, add_zero, zero_add]
end PI.NMeasInv.UnitaryGroupMassFormula
