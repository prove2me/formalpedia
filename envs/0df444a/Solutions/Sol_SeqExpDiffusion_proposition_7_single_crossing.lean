-- Prove2me | solution 1 for SeqExpDiffusion.proposition_7_single_crossing
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:01:39.732934+00:00
-- url     : https://prove2.me/submissions/cad42476-71fb-4ef0-84b6-5caa885eb6e8

import Mathlib
import Definitions.Def_SeqExpDiffusion_gammaOf
import Definitions.Def_SeqExpDiffusion_contValue

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion.Aux_SE

open SeqExpDiffusion

theorem reduce (γ C₀ C₁ D₀ D₁ δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1)
    (heq : contValue γ C₀ C₁ δ = contValue γ D₀ D₁ δ) :
    (C₀ - D₀) * (1 - δ) ^ (2 * γ - 1) + (C₁ - D₁) * δ ^ (2 * γ - 1) = 0 := by
  have hpos1 : 0 < 1 - δ := by linarith
  have e1 : (1 - δ) ^ γ = (1 - δ) ^ (1 - γ) * (1 - δ) ^ (2 * γ - 1) := by
    rw [← Real.rpow_add hpos1]; congr 1; ring
  have e2 : δ ^ γ = δ ^ (1 - γ) * δ ^ (2 * γ - 1) := by
    rw [← Real.rpow_add h0]; congr 1; ring
  unfold contValue at heq
  rw [e1, e2] at heq
  have hpre : 0 < (1 - δ) ^ (1 - γ) * δ ^ (1 - γ) :=
    mul_pos (Real.rpow_pos_of_pos hpos1 _) (Real.rpow_pos_of_pos h0 _)
  have hprod : ((1 - δ) ^ (1 - γ) * δ ^ (1 - γ)) *
      ((C₀ - D₀) * (1 - δ) ^ (2 * γ - 1) + (C₁ - D₁) * δ ^ (2 * γ - 1)) = 0 := by
    linear_combination heq
  exact (mul_eq_zero.mp hprod).resolve_left hpre.ne'

end SeqExpDiffusion.Aux_SE

open SeqExpDiffusion SeqExpDiffusion.Aux_SE in
theorem solution (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (C₀ C₁ D₀ D₁ : ℝ) (hne : (C₀, C₁) ≠ (D₀, D₁)) :
    {δ ∈ Ioo (0 : ℝ) 1 |
      contValue (gammaOf r σ) C₀ C₁ δ = contValue (gammaOf r σ) D₀ D₁ δ}.Subsingleton := by
  set γ := gammaOf r σ with hγ
  have he : 0 < 2 * γ - 1 := by
    rw [hγ]; unfold gammaOf
    have : 0 < Real.sqrt (1 + 8 * r / σ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    linarith
  set e := 2 * γ - 1 with he_def
  -- two distinct zeros force the coefficients to vanish
  have key : ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ < δ₂ → δ₂ < 1 →
      (C₀ - D₀) * (1 - δ₁) ^ e + (C₁ - D₁) * δ₁ ^ e = 0 →
      (C₀ - D₀) * (1 - δ₂) ^ e + (C₁ - D₁) * δ₂ ^ e = 0 → False := by
    intro δ₁ δ₂ h0 hlt h1 eq1 eq2
    set a := C₀ - D₀ with ha
    set b := C₁ - D₁ with hb
    have hA2 : 0 < (1 - δ₂) ^ e := Real.rpow_pos_of_pos (by linarith) _
    have hA : (1 - δ₂) ^ e < (1 - δ₁) ^ e := Real.rpow_lt_rpow (by linarith) (by linarith) he
    have hB1 : 0 < δ₁ ^ e := Real.rpow_pos_of_pos h0 _
    have hB : δ₁ ^ e < δ₂ ^ e := Real.rpow_lt_rpow h0.le hlt he
    have hdet : 0 < (1 - δ₁) ^ e * δ₂ ^ e - (1 - δ₂) ^ e * δ₁ ^ e := by nlinarith
    have hprod : a * ((1 - δ₁) ^ e * δ₂ ^ e - (1 - δ₂) ^ e * δ₁ ^ e) = 0 := by
      linear_combination δ₂ ^ e * eq1 - δ₁ ^ e * eq2
    have ha0 : a = 0 := (mul_eq_zero.mp hprod).resolve_right hdet.ne'
    rw [ha0, zero_mul, zero_add] at eq1
    have hb0 : b = 0 := (mul_eq_zero.mp eq1).resolve_right hB1.ne'
    apply hne
    rw [Prod.mk.injEq]
    constructor <;> linarith
  intro δ₁ hδ₁ δ₂ hδ₂
  obtain ⟨⟨h10, h11⟩, heq1⟩ := hδ₁
  obtain ⟨⟨h20, h21⟩, heq2⟩ := hδ₂
  have r1 := reduce γ C₀ C₁ D₀ D₁ δ₁ h10 h11 heq1
  have r2 := reduce γ C₀ C₁ D₀ D₁ δ₂ h20 h21 heq2
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact key δ₁ δ₂ h10 hlt h21 r1 r2
  · exact key δ₂ δ₁ h20 hlt h11 r2 r1
