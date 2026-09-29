-- Prove2me | solution 1 for StochLinOpt.LowerBound.round_regret_ge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:38:41.244244+00:00
-- url     : https://prove2.me/submissions/83ea63c7-acdb-4997-b14d-9815450c314e

import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open Matrix

namespace StochLinOpt.LowerBound

lemma aux_rr_optCost (μ : Fin 2 → ℝ) (hμ : μ ⬝ᵥ μ = 1 / 4) : optCost μ = -1 / 2 := by
  unfold optCost
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨![-2 * μ 0, -2 * μ 1], ?_, ?_⟩
    · show ![-2 * μ 0, -2 * μ 1] ⬝ᵥ ![-2 * μ 0, -2 * μ 1] = 1
      simp only [dotProduct, Fin.sum_univ_two] at hμ ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination 4 * hμ
    · simp only [dotProduct, Fin.sum_univ_two] at hμ ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -2 * hμ
  · rintro y ⟨x, hx, rfl⟩
    have hx' : x ⬝ᵥ x = 1 := hx
    simp only [dotProduct, Fin.sum_univ_two] at hμ hx' ⊢
    nlinarith [sq_nonneg (μ 0 + x 0 / 2), sq_nonneg (μ 1 + x 1 / 2)]

lemma aux_rr_bound (μ x : Fin 2 → ℝ) (hμ : μ ⬝ᵥ μ = 1 / 4) (hx : x ⬝ᵥ x = 1) :
    (μ ⬝ᵥ x) ^ 2 ≤ 1 / 4 := by
  simp only [dotProduct, Fin.sum_univ_two] at hμ hx ⊢
  have h : (μ 0 * μ 0 + μ 1 * μ 1) * (x 0 * x 0 + x 1 * x 1) = 1 / 4 := by
    rw [hμ, hx]; norm_num
  nlinarith [sq_nonneg (μ 0 * x 1 - μ 1 * x 0)]

lemma aux_rr_gram (a1 a2 b1 b2 x1 x2 E : ℝ) (hA : a1 * a1 + a2 * a2 = 1 / 4)
    (hB : b1 * b1 + b2 * b2 = 1 / 4) (hD : (a1 - b1) * (a1 - b1) + (a2 - b2) * (a2 - b2) = E)
    (hX : x1 * x1 + x2 * x2 = 1) :
    ((a1 * x1 + a2 * x2) - (b1 * x1 + b2 * x2)) ^ 2 =
      E * (1 - E - 4 * (a1 * x1 + a2 * x2) * (b1 * x1 + b2 * x2)) := by
  have hg : a1 * b1 + a2 * b2 = 1 / 4 - E / 2 := by
    linear_combination (hA + hB - hD) / 2
  have hT : (a1 * x1 + a2 * x2) ^ 2 + (b1 * x1 + b2 * x2) ^ 2
      - 8 * (a1 * b1 + a2 * b2) * (a1 * x1 + a2 * x2) * (b1 * x1 + b2 * x2)
      + 4 * (a1 * b1 + a2 * b2) ^ 2 - 1 / 4 = 0 := by
    linear_combination (-4 * (b1 * x1 + b2 * x2) ^ 2
        + 4 * (b1 * b1 + b2 * b2) * (x1 * x1 + x2 * x2)) * hA
      + (-4 * (a1 * x1 + a2 * x2) ^ 2 + (x1 * x1 + x2 * x2)) * hB
      + (-4 * (a1 * b1 + a2 * b2) ^ 2 + 1 / 4) * hX
  linear_combination hT + (8 * (a1 * x1 + a2 * x2) * (b1 * x1 + b2 * x2)
      - 4 * ((a1 * b1 + a2 * b2) + 1 / 4 - E / 2)) * hg

lemma aux_rr_key (μ₁ μ₂ x : Fin 2 → ℝ) (E : ℝ) (hμ₁ : μ₁ ⬝ᵥ μ₁ = 1 / 4)
    (hμ₂ : μ₂ ⬝ᵥ μ₂ = 1 / 4) (hdist : (μ₁ - μ₂) ⬝ᵥ (μ₁ - μ₂) = E) (hx : x ⬝ᵥ x = 1) :
    (μ₁ ⬝ᵥ x - μ₂ ⬝ᵥ x) ^ 2 = E * (1 - E - 4 * (μ₁ ⬝ᵥ x) * (μ₂ ⬝ᵥ x)) := by
  simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply] at hμ₁ hμ₂ hdist hx ⊢
  exact aux_rr_gram (μ₁ 0) (μ₁ 1) (μ₂ 0) (μ₂ 1) (x 0) (x 1) E hμ₁ hμ₂ hdist hx

lemma aux_rr_main (a b p ℓ E : ℝ) (hE : 0 < E) (ha : a ^ 2 ≤ 1 / 4) (hb : b ^ 2 ≤ 1 / 4)
    (hkey : (a - b) ^ 2 = E * (1 - E - 4 * a * b)) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hℓ : ℓ = 1 ∨ ℓ = -1) :
    1 / 16 * (E + ((p * (1 + ℓ * a) - (1 - p) * (1 + ℓ * b)) /
      (p * (1 + ℓ * a) + (1 - p) * (1 + ℓ * b)) - (2 * p - 1)) ^ 2 / E) *
        (if |2 * p - 1| ≤ 1 / 2 then 1 else 0) ≤
      p * (a - -1 / 2) + (1 - p) * (b - -1 / 2) := by
  have ha1 : -1 / 2 ≤ a := by nlinarith
  have ha2 : a ≤ 1 / 2 := by nlinarith
  have hb1 : -1 / 2 ≤ b := by nlinarith
  have hb2 : b ≤ 1 / 2 := by nlinarith
  have hD : p * (1 + ℓ * a) + (1 - p) * (1 + ℓ * b) = 1 + ℓ * (p * a + (1 - p) * b) := by ring
  have hc1 : -1 / 2 ≤ p * a + (1 - p) * b := by
    nlinarith [mul_nonneg hp₀ (by linarith : (0:ℝ) ≤ a + 1 / 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (by linarith : (0:ℝ) ≤ b + 1 / 2)]
  have hc2 : p * a + (1 - p) * b ≤ 1 / 2 := by
    nlinarith [mul_nonneg hp₀ (by linarith : (0:ℝ) ≤ 1 / 2 - a),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (by linarith : (0:ℝ) ≤ 1 / 2 - b)]
  have hDpos : 1 / 2 ≤ 1 + ℓ * (p * a + (1 - p) * b) := by
    rcases hℓ with rfl | rfl <;> linarith
  have hℓ2 : ℓ ^ 2 = 1 := by rcases hℓ with rfl | rfl <;> norm_num
  have hF : 0 ≤ 1 - E - 4 * a * b := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg (a - b), mul_neg_of_pos_of_neg hE h]
  have hnum : (p * (1 + ℓ * a) - (1 - p) * (1 + ℓ * b)) /
      (p * (1 + ℓ * a) + (1 - p) * (1 + ℓ * b)) - (2 * p - 1) =
      2 * p * (1 - p) * ℓ * (a - b) / (1 + ℓ * (p * a + (1 - p) * b)) := by
    rw [hD]
    have hne : (1 + ℓ * (p * a + (1 - p) * b)) ≠ 0 := by linarith
    field_simp
    ring
  have hsq : (2 * p * (1 - p) * ℓ * (a - b) / (1 + ℓ * (p * a + (1 - p) * b))) ^ 2 / E =
      4 * (p * (1 - p)) ^ 2 * (1 - E - 4 * a * b) / (1 + ℓ * (p * a + (1 - p) * b)) ^ 2 := by
    have hne : (1 + ℓ * (p * a + (1 - p) * b)) ≠ 0 := by linarith
    rw [div_pow, div_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (4 * (p * (1 - p)) ^ 2 * (1 + ℓ * (p * a + (1 - p) * b)) ^ 2 * ℓ ^ 2) * hkey
      + (4 * (p * (1 - p)) ^ 2 * (1 + ℓ * (p * a + (1 - p) * b)) ^ 2 * E
        * (1 - E - 4 * a * b)) * hℓ2
  have hRHS : p * (a - -1 / 2) + (1 - p) * (b - -1 / 2) = 1 / 2 + (p * a + (1 - p) * b) := by
    ring
  rw [hRHS]
  split_ifs with hp
  · have hp' := abs_le.mp hp
    rw [hnum, hsq, mul_one]
    set c := p * a + (1 - p) * b with hc
    set D := 1 + ℓ * c with hDdef
    set F := 1 - E - 4 * a * b with hFdef
    have hD2 : 1 / 4 ≤ D ^ 2 := by
      have := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1 / 2) hDpos
      rw [sq]; linarith
    have hq0 : 0 ≤ p * (1 - p) := mul_nonneg hp₀ (by linarith)
    have hq1 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    have hq2 : 16 * (p * (1 - p)) ^ 2 ≤ 1 := by nlinarith [mul_le_mul hq1 hq1 hq0 (by norm_num)]
    have h1 : 4 * (p * (1 - p)) ^ 2 * F / D ^ 2 ≤ 16 * (p * (1 - p)) ^ 2 * F := by
      rw [div_le_iff₀ (by positivity)]
      have h0 : 0 ≤ (p * (1 - p)) ^ 2 * F := mul_nonneg (sq_nonneg _) hF
      have := mul_le_mul_of_nonneg_left hD2 h0
      linarith
    have h2 : 16 * (p * (1 - p)) ^ 2 * F ≤ F := by
      have := mul_le_mul_of_nonneg_right hq2 hF
      linarith
    have h3 : E + F ≤ 8 + 16 * c := by
      rw [hFdef, hc]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a + 1 / 2) (by linarith : (0:ℝ) ≤ b + 1 / 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ p - 1 / 8) (by linarith : (0:ℝ) ≤ a + 1 / 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ 7 / 8 - p) (by linarith : (0:ℝ) ≤ b + 1 / 2)]
    linarith
  · rw [mul_zero]
    linarith

end StochLinOpt.LowerBound

open StochLinOpt.LowerBound

theorem solution (μ₁ μ₂ x : Fin 2 → ℝ) (ε p ℓ : ℝ)
    (hμ₁ : μ₁ ⬝ᵥ μ₁ = 1 / 4) (hμ₂ : μ₂ ⬝ᵥ μ₂ = 1 / 4)
    (hε : 0 < ε) (hdist : (μ₁ - μ₂) ⬝ᵥ (μ₁ - μ₂) = ε ^ 2) (hx : x ∈ unitCircle)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hℓ : ℓ = 1 ∨ ℓ = -1) :
    1 / 16 * (ε ^ 2 + (biasUpdate μ₁ μ₂ x p ℓ - (2 * p - 1)) ^ 2 / ε ^ 2) *
        (if |2 * p - 1| ≤ 1 / 2 then 1 else 0) ≤
      p * (μ₁ ⬝ᵥ x - optCost μ₁) + (1 - p) * (μ₂ ⬝ᵥ x - optCost μ₂) := by
  have hx' : x ⬝ᵥ x = 1 := hx
  rw [aux_rr_optCost μ₁ hμ₁, aux_rr_optCost μ₂ hμ₂]
  unfold biasUpdate
  exact aux_rr_main _ _ p ℓ (ε ^ 2) (by positivity) (aux_rr_bound μ₁ x hμ₁ hx')
    (aux_rr_bound μ₂ x hμ₂ hx') (aux_rr_key μ₁ μ₂ x _ hμ₁ hμ₂ hdist hx') hp₀ hp₁ hℓ
