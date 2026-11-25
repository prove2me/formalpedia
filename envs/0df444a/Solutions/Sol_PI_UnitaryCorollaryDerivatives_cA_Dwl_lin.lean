-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dwl_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:02:51.336586+00:00
-- url     : https://prove2.me/submissions/bb1d8477-77fd-4afd-8fea-ad919036f1e9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dx_lin
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_smooth

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
theorem _root_.solution (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F₁ F₂ : B.Mat k r → E}
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁) (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₂) (c : ℂ) :
    Dwl lam w (fun g => F₁ g + c • F₂ g) = fun g => Dwl lam w F₁ g + c • Dwl lam w F₂ g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have d₁ := (cA_Dwl_smooth lam w h₁).differentiable (by simp)
    have d₂ := (cA_Dwl_smooth lam w h₂).differentiable (by simp)
    show (fun g => Dx x (Dwl lam w _) g + lam x • Dwl lam w _ g) = _
    rw [ih, cA_Dx_lin x d₁ d₂ c]
    funext g
    show _ = (Dx x (Dwl lam w F₁) g + lam x • Dwl lam w F₁ g) + c • (Dx x (Dwl lam w F₂) g + lam x • Dwl lam w F₂ g)
    rw [smul_add, smul_add, smul_comm c (lam x)]
    exact add_add_add_comm _ _ _ _
end PI.UnitaryCorollaryDerivatives
