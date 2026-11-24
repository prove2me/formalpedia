-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dx_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:45.123409+00:00
-- url     : https://prove2.me/submissions/af052d37-05df-4885-8b73-b53db9595826

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_hasDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dirL_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (x : Bool × B.Mat k r) {F : B.Mat k r → E} (hd : Differentiable ℝ F) :
    Dx x F = fun g => fderiv ℝ F g (dirL x g) := by
  funext g
  rw [Dx_eq, dirL_apply]
  exact (cA_hasDeriv x (hd g)).deriv
end PI.UnitaryCorollaryDerivatives
