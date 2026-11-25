-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BridgeRealK.jm_mul_jm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:52:52.885593+00:00
-- url     : https://prove2.me/submissions/0d7d8527-d2d6-4066-9699-5b0f84341bca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealFieldComparison_JmMulApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BridgeRealK_jm_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_BridgeRealK_sgn_mul_self

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact sgn_mul_self ε a
end PI.UnitaryGroupMassFormula.BridgeRealK
