-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_exists_SL_smul_eq_df0b2626b635
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:43:06.696071+00:00
-- url     : https://prove2.me/submissions/6dd00bfc-8c29-460a-ac90-6fda6fba7b3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups
open GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
namespace GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
theorem _root_.solution {τ τ' : ℍ} {μ : ℂ} (hμ : μ ≠ 0)
    (h1 : ∀ z ∈ latticeOf (τ : ℂ), μ * z ∈ latticeOf (τ' : ℂ))
    (h2 : ∀ w ∈ latticeOf (τ' : ℂ), μ⁻¹ * w ∈ latticeOf (τ : ℂ)) :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by

  obtain ⟨d, c, hdc⟩ := mem_latticeOf.mp (h2 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨b, a, hba⟩ := mem_latticeOf.mp (h2 τ' (mem_latticeOf.mpr ⟨0, 1, by simp⟩))

  obtain ⟨h, g, hhg⟩ := mem_latticeOf.mp (h1 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩))
  obtain ⟨f, e, hfe⟩ := mem_latticeOf.mp (h1 τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩))
  rw [mul_one] at hdc hhg

  have k1 : ((d * h + c * f : ℤ) : ℂ) + ((d * g + c * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination hinv - μ * hdc - (d : ℂ) * hhg - (c : ℂ) * hfe
  have k2 : ((b * h + a * f : ℤ) : ℂ) + ((b * g + a * e : ℤ) : ℂ) * (τ' : ℂ) =
      ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ' : ℂ) := by
    have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    push_cast
    linear_combination (τ' : ℂ) * hinv - μ * hba - (b : ℂ) * hhg - (a : ℂ) * hfe
  obtain ⟨E4, E3⟩ := coord_unique k1
  obtain ⟨E2, E1⟩ := coord_unique k2
  have hdet1 : (a * d - b * c) * (e * h - f * g) = 1 := by
    linear_combination (c * f + d * h) * E1 + E4 - (c * e + d * g) * E2

  have hw : (c : ℂ) * τ + d ≠ 0 := by
    rw [add_comm, ← hdc]; exact inv_ne_zero hμ
  have hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / ((c : ℂ) * τ + d) := by
    rw [eq_div_iff hw, add_comm ((c : ℂ) * τ), ← hdc, add_comm ((a : ℂ) * τ), ← hba]
    field_simp

  have hdetpos : 0 < a * d - b * c := by
    have him := congr_arg Complex.im hτ'
    rw [Complex.div_im] at him
    have hN : 0 < Complex.normSq ((c : ℂ) * τ + d) := Complex.normSq_pos.mpr hw
    have key : (τ' : ℂ).im * Complex.normSq ((c : ℂ) * τ + d) = ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [him, sub_mul, div_mul_cancel₀ _ hN.ne', div_mul_cancel₀ _ hN.ne']
      simp
      ring
    have : (0 : ℝ) < ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      rw [← key]; exact mul_pos τ'.im_pos hN
    have := (pos_of_mul_pos_left this τ.im_pos.le)
    exact_mod_cast this
  have hdet : a * d - b * c = 1 :=
    Int.eq_one_of_mul_eq_one_right hdetpos.le hdet1
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨γ, UpperHalfPlane.ext ?_⟩
  rw [coe_specialLinearGroup_apply, hτ']
  simp [γ]
end GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
