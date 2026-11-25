-- Prove2me | solution 1 for PI.SSE.reduce_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:03.982233+00:00
-- url     : https://prove2.me/submissions/5e201a02-4fea-448b-93ea-e3a1a62ad2e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Reduce
import Theorems.Thm_PI_SSE_integer_combination_mem_lattice
import Theorems.Thm_PI_SSE_lattice_span_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Modular
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (w₁ w₂ : ℂ) (hw : 0 < ((starRingEnd ℂ) w₁ * w₂).im) :
    ∃ v₁ v₂ : ℂ, v₁ ≠ 0 ∧ PI.lat2 v₁ v₂ = PI.lat2 w₁ w₂ ∧ 0 < (v₂ / v₁).im ∧
      3 ≤ 4 * (v₂ / v₁).im ^ 2 := by
  have hw1 : w₁ ≠ 0 := by
    rintro rfl
    simp at hw
  have hN : 0 < Complex.normSq w₁ := Complex.normSq_pos.mpr hw1
  have him : 0 < (w₂ / w₁).im := by
    have e : (w₂ / w₁).im = ((starRingEnd ℂ) w₁ * w₂).im / Complex.normSq w₁ := by
      simp only [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [e]
    exact div_pos hw hN
  let τ : UpperHalfPlane := ⟨w₂ / w₁, him⟩
  have hτ : (τ : ℂ) = w₂ / w₁ := rfl
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
  have hcoe := UpperHalfPlane.coe_specialLinearGroup_apply g τ
  have hdet0 := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet0
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hc, ← hd] at hdet0 hcoe
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at hcoe
  have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet0
  have hden : (c : ℂ) * (w₂ / w₁) + d ≠ 0 := by
    intro h0
    have e1 : ((c : ℂ) * (w₂ / w₁) + d).im = c * (w₂ / w₁).im := by simp
    have e2 : ((c : ℂ) * (w₂ / w₁) + d).re = c * (w₂ / w₁).re + d := by simp
    rw [h0] at e1 e2
    simp only [Complex.zero_im, Complex.zero_re] at e1 e2
    have hc0 : (c : ℝ) = 0 := by
      rcases mul_eq_zero.mp e1.symm with h | h
      · exact h
      · linarith
    have hd0 : (d : ℝ) = 0 := by
      rw [hc0, zero_mul, zero_add] at e2
      linarith
    have hc0' : c = 0 := by exact_mod_cast hc0
    have hd0' : d = 0 := by exact_mod_cast hd0
    rw [hc0', hd0'] at hdet0
    simp at hdet0
  have hv1 : (c : ℂ) * w₂ + d * w₁ = w₁ * ((c : ℂ) * (w₂ / w₁) + d) := by
    field_simp
  have hv2 : (a : ℂ) * w₂ + b * w₁ = w₁ * ((a : ℂ) * (w₂ / w₁) + b) := by
    field_simp
  have hv1ne : (c : ℂ) * w₂ + d * w₁ ≠ 0 := by
    rw [hv1]
    exact mul_ne_zero hw1 hden
  have hq : ((a : ℂ) * w₂ + b * w₁) / ((c : ℂ) * w₂ + d * w₁) = ((g • τ : UpperHalfPlane) : ℂ) := by
    rw [hcoe, hτ, hv1, hv2, mul_div_mul_left _ _ hw1]
  refine ⟨(c : ℂ) * w₂ + d * w₁, (a : ℂ) * w₂ + b * w₁, hv1ne, le_antisymm ?_ ?_, ?_, ?_⟩
  · apply lattice_span_le
    · have := integer_combination_mem_lattice w₁ w₂ d c
      rwa [add_comm] at this
    · have := integer_combination_mem_lattice w₁ w₂ b a
      rwa [add_comm] at this
  · apply lattice_span_le
    · have := integer_combination_mem_lattice ((c : ℂ) * w₂ + d * w₁) ((a : ℂ) * w₂ + b * w₁) a (-c)
      convert this using 1
      push_cast
      linear_combination (-w₁) * hdetC
    · have := integer_combination_mem_lattice ((c : ℂ) * w₂ + d * w₁) ((a : ℂ) * w₂ + b * w₁) (-b) d
      convert this using 1
      push_cast
      linear_combination (-w₂) * hdetC
  · rw [hq, UpperHalfPlane.coe_im]
    exact UpperHalfPlane.im_pos _
  · rw [hq, UpperHalfPlane.coe_im]
    exact h3
end PI.SSE
