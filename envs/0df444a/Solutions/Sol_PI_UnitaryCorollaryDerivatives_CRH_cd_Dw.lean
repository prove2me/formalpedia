-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.cd_Dw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:38.842408+00:00
-- url     : https://prove2.me/submissions/ce12e996-7fc4-42a4-841f-111cf609521c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cd_Dx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.CRH
theorem _root_.solution (w : List (Bool × Mat k r)) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact cd_Dx x ih
end PI.UnitaryCorollaryDerivatives.CRH
