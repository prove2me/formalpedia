-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BridgeRealK.jm_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:23.655463+00:00
-- url     : https://prove2.me/submissions/390c4d1f-9240-48b5-94a4-db632d5d04ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealFieldComparison_JmMulApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BridgeRealK_jm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BridgeRealK
open Matrix
namespace PI.UnitaryGroupMassFormula.BridgeRealK
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Formalism.REAL.Jm ε * k) a b = (if ε a then (1 : ℂ) else -1) * k a b := by
  rw [jm_eq, Matrix.diagonal_mul]
end PI.UnitaryGroupMassFormula.BridgeRealK
