-- Prove2me | solution 1 for P2M_PI_UnitaryCorollaryDerivatives_CCA_Dw_add__1dc732627764
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:27.373918+00:00
-- url     : https://prove2.me/submissions/63553740-8783-4617-8b93-7da0c52b2332

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_sm_diff
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_sm_Dw
import Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CCA_Dx_add__f7aedbeca0a8

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
theorem _root_.solution (w : List (Bool × Mat k r)) {f₁ f₂ : Mat k r → ℂ} (h₁ : ContDiff ℝ ∞ f₁)
    (h₂ : ContDiff ℝ ∞ f₂) : Dw w (fun g => f₁ g + f₂ g) = fun g => Dw w f₁ g + Dw w f₂ g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => f₁ g + f₂ g) = _
    rw [ih]
    exact Dx_add' x (sm_diff (sm_Dw w h₁)) (sm_diff (sm_Dw w h₂))
end PI.UnitaryCorollaryDerivatives.CCA
