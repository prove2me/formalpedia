-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.exp_add_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:20.233907+00:00
-- url     : https://prove2.me/submissions/c8a12326-fb86-44dc-aac0-53e234fbc321

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
theorem _root_.solution (Y : Matrix (Fin N) (Fin N) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) = NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y) := by
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)
end PI.UnitaryCorollaryDerivatives.DjC
