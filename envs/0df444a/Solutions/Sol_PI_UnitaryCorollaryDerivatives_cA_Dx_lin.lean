-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dx_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:53:56.294936+00:00
-- url     : https://prove2.me/submissions/8ce59498-6133-49ce-8a22-124452020287

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_hasDeriv

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
theorem _root_.solution (x : Bool × B.Mat k r) {F₁ F₂ : B.Mat k r → E} (h₁ : Differentiable ℝ F₁)
    (h₂ : Differentiable ℝ F₂) (c : ℂ) :
    Dx x (fun g => F₁ g + c • F₂ g) = fun g => Dx x F₁ g + c • Dx x F₂ g := by
  funext g
  rw [Dx_eq, Dx_eq, Dx_eq, (cA_hasDeriv x (h₁ g)).deriv, (cA_hasDeriv x (h₂ g)).deriv]
  exact ((cA_hasDeriv x (h₁ g)).add ((cA_hasDeriv x (h₂ g)).const_smul c)).deriv
end PI.UnitaryCorollaryDerivatives
