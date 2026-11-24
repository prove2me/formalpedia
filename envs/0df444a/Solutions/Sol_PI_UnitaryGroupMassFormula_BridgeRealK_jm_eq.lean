-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BridgeRealK.jm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:18:48.797802+00:00
-- url     : https://prove2.me/submissions/60e367b4-1d9c-4896-a2d1-a5dbba7fb21c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealFieldComparison_JmMulApply

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl
end PI.UnitaryGroupMassFormula.BridgeRealK
