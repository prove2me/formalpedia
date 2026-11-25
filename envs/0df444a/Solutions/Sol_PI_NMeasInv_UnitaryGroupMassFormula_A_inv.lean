-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.A_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:16.370131+00:00
-- url     : https://prove2.me/submissions/6eb93c67-96be-4505-ae1a-c3bd688bc086

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_A
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_one
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
theorem _root_.solution (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) (v : Fin n → ℂ) :
    Afun ε e f s (Afun ε e f s⁻¹ v) = v := by
  rw [A_A hG, show s * s⁻¹ = 1 from funext fun b => by simp [hs b], A_one hG]
end PI.NMeasInv.UnitaryGroupMassFormula
