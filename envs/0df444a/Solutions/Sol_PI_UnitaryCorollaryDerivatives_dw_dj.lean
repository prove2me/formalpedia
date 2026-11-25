-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.dw_dj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:04.50379+00:00
-- url     : https://prove2.me/submissions/795dec77-38b3-4f65-863c-2917428b2f26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_MxLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_smul


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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (h1 : DjCurve) (k j ρ : ℕ) : ∀ w : List (Bool × B.Mat k (j + ρ)),
    (∀ x ∈ w, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1) →
    ∃ K : ℂ, ‖K‖ ≤ (j : ℝ) ^ w.length ∧ ∀ g, Dw w (DjU k j ρ) g = K * DjU k j ρ g := by
  intro w
  induction w with
  | nil => intro _; exact ⟨1, by simp, fun g => by simp [Dw]⟩
  | cons x w ih =>
    intro hw
    obtain ⟨K, hK, hD⟩ := ih fun y hy => hw y (by simp [hy])
    obtain ⟨hxP, hxm⟩ := hw x (by simp)
    obtain ⟨c₁, c₂, hc₁, hc₂, hcur⟩ := h1 k j ρ x.2 hxP
    have hderiv : ∀ (c D : ℂ), HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c) * D) (c * D) 0 := by
      intro c D
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) (1 * c) 0 :=
        (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c
      have := (h0.cexp).mul_const D
      simpa using this
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    obtain ⟨b, X⟩ := x
    cases b
    · refine ⟨c₁ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₁.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((false, X) :: w) (DjU k j ρ) = Dx (false, X) (fun g => K • DjU k j ρ g) := by
          show Dx (false, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (false, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (false, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g := by
          funext t; exact (hcur g t).1
        simp only [e2, (hderiv c₁ _).deriv, smul_eq_mul]
        ring
    · refine ⟨c₂ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₂.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((true, X) :: w) (DjU k j ρ) = Dx (true, X) (fun g => K • DjU k j ρ g) := by
          show Dx (true, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (true, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (true, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g := by
          funext t; exact (hcur g t).2
        simp only [e2, (hderiv c₂ _).deriv, smul_eq_mul]
        ring
end PI.UnitaryCorollaryDerivatives
