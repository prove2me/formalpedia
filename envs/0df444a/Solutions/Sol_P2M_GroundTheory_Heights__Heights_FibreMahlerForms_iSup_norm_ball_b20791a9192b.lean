-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_iSup_norm_ball_b20791a9192b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:14.09569+00:00
-- url     : https://prove2.me/submissions/b39c91dd-2824-4690-93e1-d534acc5061c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreMahlerForms_apply_eq_sum_1364e9b5a1d6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FibreMahlerForms
theorem _root_.solution (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) :
    ⨆ ξ : {ξ : V // ‖ξ‖ ≤ 1}, ‖ℓ ξ‖ = √(∑ j, ‖ℓ (b j)‖ ^ 2) := by
  set v : V := ∑ j, star (ℓ (b j)) • b j
  have hv : ∀ ξ, ℓ ξ = inner ℂ v ξ := by
    intro ξ
    rw [apply_eq_sum b ℓ ξ]
    simp only [v, sum_inner, inner_smul_left, Complex.star_def, Complex.conj_conj]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hvv : ‖v‖ = √(∑ j, ‖ℓ (b j)‖ ^ 2) := by
    have h2 : ‖v‖ ^ 2 = ∑ j, ‖ℓ (b j)‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, ← hv]
      simp only [v, map_sum, map_smul, smul_eq_mul, Complex.star_def, Complex.conj_mul',
        ← Complex.ofReal_pow, RCLike.re_to_complex, Complex.ofReal_re]
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [← hvv]
  have hle : ∀ ξ : {ξ : V // ‖ξ‖ ≤ 1}, ‖ℓ ξ‖ ≤ ‖v‖ := fun ξ ↦ by
    rw [hv]
    calc ‖inner ℂ v (ξ : V)‖ ≤ ‖v‖ * ‖(ξ : V)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * 1 := by gcongr; exact ξ.2
      _ = ‖v‖ := mul_one _
  have : Nonempty {ξ : V // ‖ξ‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  refine le_antisymm (ciSup_le hle) ?_
  have hbdd : BddAbove (Set.range fun ξ : {ξ : V // ‖ξ‖ ≤ 1} ↦ ‖ℓ ξ‖) := ⟨‖v‖, by
    rintro _ ⟨ξ, rfl⟩; exact hle ξ⟩
  by_cases h0 : v = 0
  · rw [h0, norm_zero]
    exact le_trans (norm_nonneg _) (le_ciSup hbdd ⟨0, by simp⟩)
  · have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
    refine le_trans (le_of_eq ?_) (le_ciSup hbdd ⟨(‖v‖ : ℂ)⁻¹ • v, ?_⟩)
    · have hn' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      rw [hv, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), norm_mul, norm_inv, norm_pow]
      simp only [Complex.norm_real, RCLike.norm_ofReal, Real.norm_eq_abs, abs_norm]
      field_simp
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
end GroundTheory.Heights₂.Heights.FibreMahlerForms
