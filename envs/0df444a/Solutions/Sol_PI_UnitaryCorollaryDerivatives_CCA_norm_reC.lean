-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CCA.norm_reC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:28.735706+00:00
-- url     : https://prove2.me/submissions/f73446fb-91de-486d-8de7-3845c362805a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_reC_apply

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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CCA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.CCA
theorem _root_.solution (z : ℂ) : ‖reC z‖ ≤ ‖z‖ := by
  rw [reC_apply, Complex.norm_real, Real.norm_eq_abs]
  first
  | exact Complex.abs_re_le_norm z
  | exact Complex.abs_re_le_abs z
end PI.UnitaryCorollaryDerivatives.CCA
