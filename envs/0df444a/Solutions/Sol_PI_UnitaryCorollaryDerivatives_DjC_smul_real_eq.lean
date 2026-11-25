-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.smul_real_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:29.281009+00:00
-- url     : https://prove2.me/submissions/6d805dd8-0f5d-4a66-b774-bd973a676ec5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {N j : ℕ}
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (Y : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) : (t : ℂ) • Y = t • Y := by
  ext a b
  simp
end PI.UnitaryCorollaryDerivatives.DjC
