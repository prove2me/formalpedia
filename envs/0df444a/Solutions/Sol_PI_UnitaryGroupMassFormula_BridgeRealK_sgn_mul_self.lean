-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BridgeRealK.sgn_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:31.0608+00:00
-- url     : https://prove2.me/submissions/66004510-c102-43e3-8123-958aecc34640

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealFieldComparison_JmMulApply
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BridgeRealK
open Matrix
namespace PI.UnitaryGroupMassFormula.BridgeRealK
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (if ε a then (1 : ℂ) else -1) * (if ε a then (1 : ℂ) else -1) = 1 := by
  cases ε a <;> simp
end PI.UnitaryGroupMassFormula.BridgeRealK
