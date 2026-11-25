-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dw_expmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:11.458306+00:00
-- url     : https://prove2.me/submissions/fc85fe9f-5207-49af-928f-f4eb0831edd0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_hasDeriv
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dx_eq
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
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
theorem _root_.solution (lam : Bool × B.Mat k r → ℂ) (h : B.Mat k r → ℂ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ∀ g (t : ℝ), h (crv x g t) = Complex.exp ((t : ℂ) * lam x) * h g) →
      Dw w (fun g => h g • F g) = fun g => h g • Dwl lam w F g := by
  intro w
  induction w with
  | nil => intro F _ _; rfl
  | cons x w ih =>
    intro F hF hh
    have hh' : ∀ y ∈ w, ∀ g (t : ℝ), h (crv y g t) = Complex.exp ((t : ℂ) * lam y) * h g :=
      fun y hy => hh y (by simp [hy])
    show Dx x (Dw w _) = _
    rw [ih F hF hh']
    funext g
    have hG := cA_Dwl_smooth lam w hF
    have d := cA_hasDeriv x ((hG.differentiable (by simp)) g)
    have he : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * lam x) * h g) (lam x * h g) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam x) (1 * lam x) 0 :=
        (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (lam x)
      have h2 := (h1.cexp).mul_const (h g)
      simpa using h2
    have hs : HasDerivAt (fun t : ℝ => (Complex.exp ((t : ℂ) * lam x) * h g) • Dwl lam w F (crv x g t))
        ((Complex.exp (((0 : ℝ) : ℂ) * lam x) * h g) • fderiv ℝ (Dwl lam w F) g (dirv x g) +
          (lam x * h g) • Dwl lam w F (crv x g 0)) 0 := he.smul d
    rw [Dx_eq]
    have e : (fun t : ℝ => h (crv x g t) • Dwl lam w F (crv x g t)) =
        fun t : ℝ => (Complex.exp ((t : ℂ) * lam x) * h g) • Dwl lam w F (crv x g t) := by
      funext t; rw [hh x (by simp) g t]
    rw [e, hs.deriv, crv_zero, ← dirL_apply, ← congrFun (cA_Dx_eq x (hG.differentiable (by simp))) g]
    show _ = h g • (Dx x (Dwl lam w F) g + lam x • Dwl lam w F g)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, smul_add, smul_smul]
    rw [mul_comm (lam x)]
end PI.UnitaryCorollaryDerivatives
