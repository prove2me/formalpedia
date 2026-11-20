-- Prove2me | solution 1 for ProbabilityTheory.lintegral_sup_rpow_edist_le_of_minimal_cover_two
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:10:01.84327+00:00
-- url     : https://prove2.me/submissions/535e1f77-35df-45f2-95a9-a68099f11fff

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal Finset

section Aux

end Aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

end Measurability

section FirstTerm

variable {J : Set T}

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

theorem _root_.solution (hp : 1 ≤ p)
    (hX : IsAEKolmogorovProcess X P p q M) {ε₀ : ℝ≥0} (hε : ε₀ ≤ Metric.ediam J)
    (hC : ∀ n, IsCover (ε₀ * 2⁻¹ ^ n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J)
    (hC_card : ∀ n, #(C n) = coveringNumber (ε₀ * 2⁻¹ ^ n) J)
    {c₁ : ℝ≥0∞} {d : ℝ} (hdq : d < q)
    (h_cov : HasBoundedCoveringNumber J c₁ d)
    (hm : m ≤ k) :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ 2 ^ d * M * c₁ * (2 * (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) / (2 ^ ((q - d) / p) - 1) ^ p := by
  have hp0 : 0 < p := hX.p_pos
  have hq0 : 0 < q := hX.q_pos
  have hεJ : ∀ n, ((ε₀ * 2⁻¹ ^ n : ℝ≥0) : ℝ≥0∞) ≤ Metric.ediam J := by
    intro n
    refine le_trans ?_ hε
    exact ENNReal.coe_le_coe.mpr (mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by positivity) (by norm_num)))
  refine (lintegral_sup_rpow_edist_le_of_minimal_cover (ε := fun n => ε₀ * 2⁻¹ ^ n) hp hX hεJ hC
    hC_subset hC_card h_cov hm).trans ?_
  set s := (q - d) / p with hs
  have hs0 : 0 < s := div_pos (by linarith) hp0
  rcases eq_or_ne ε₀ 0 with h0 | h0
  · subst h0
    have hz : ∀ j : ℕ, (((0 : ℝ≥0) * 2⁻¹ ^ (m + j + 1) : ℝ≥0) : ℝ≥0∞) ^ (-d / p) *
        (((0 : ℝ≥0) * 2⁻¹ ^ (m + j) : ℝ≥0) : ℝ≥0∞) ^ (q / p) = 0 := by
      intro j
      simp [ENNReal.zero_rpow_of_pos (div_pos hq0 hp0)]
    simp only [hz, Finset.sum_const_zero, ENNReal.zero_rpow_of_pos hp0, mul_zero]
    exact bot_le
  · set c0 : ℝ≥0∞ := (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m with hc0def
    have hc0 : c0 ≠ 0 := by
      rw [hc0def]; exact mul_ne_zero (by simpa using h0) (pow_ne_zero _ (by norm_num))
    have hc0t : c0 ≠ ⊤ := by
      rw [hc0def]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top (by norm_num))
    have hterm : ∀ j : ℕ, ((ε₀ * 2⁻¹ ^ (m + j + 1) : ℝ≥0) : ℝ≥0∞) ^ (-d / p) *
        ((ε₀ * 2⁻¹ ^ (m + j) : ℝ≥0) : ℝ≥0∞) ^ (q / p) =
        2 ^ (d / p) * (c0 ^ s * ((2⁻¹ : ℝ≥0∞) ^ s) ^ j) := by
      intro j
      have hb : ((ε₀ * 2⁻¹ ^ (m + j) : ℝ≥0) : ℝ≥0∞) = c0 * 2⁻¹ ^ j := by
        rw [hc0def]; push_cast; rw [pow_add]; ring
      have hb1 : ((ε₀ * 2⁻¹ ^ (m + j + 1) : ℝ≥0) : ℝ≥0∞) = c0 * 2⁻¹ ^ j * 2⁻¹ := by
        rw [hc0def]; push_cast; rw [pow_succ, pow_add]; ring
      rw [hb, hb1]
      have hB0 : c0 * 2⁻¹ ^ j ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ (by norm_num))
      have hBt : c0 * 2⁻¹ ^ j ≠ ⊤ := ENNReal.mul_ne_top hc0t (ENNReal.pow_ne_top (by norm_num))
      rw [ENNReal.mul_rpow_of_ne_zero hB0 (by norm_num : (2⁻¹ : ℝ≥0∞) ≠ 0)]
      rw [mul_comm ((c0 * 2⁻¹ ^ j) ^ (-d / p)) _, mul_assoc, ← ENNReal.rpow_add _ _ hB0 hBt]
      have hx : -d / p + q / p = s := by rw [hs]; ring
      rw [hx, ENNReal.inv_rpow, ← ENNReal.rpow_neg, neg_div, neg_neg,
        ENNReal.mul_rpow_of_ne_zero hc0 (pow_ne_zero _ (by norm_num)), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm (j : ℝ) s]
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, ← Finset.mul_sum]
    set r : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ s with hr
    have hr1 : r < 1 := ENNReal.rpow_lt_one (by norm_num) hs0
    have hgeo : ∑ j ∈ Finset.range (k - m), r ^ j ≤ (1 - r)⁻¹ :=
      (ENNReal.sum_le_tsum _).trans (ENNReal.tsum_geometric r).le
    have h2s : (1 : ℝ≥0∞) < 2 ^ s := ENNReal.one_lt_rpow (by norm_num) hs0
    have h2st : (2 : ℝ≥0∞) ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs0.le (by norm_num)
    have h2s0 : (2 : ℝ≥0∞) ^ s ≠ 0 := (zero_lt_one.trans h2s).ne'
    have hrinv : r = (2 ^ s)⁻¹ := by rw [hr, ENNReal.inv_rpow]
    have h1r : (1 - r)⁻¹ = 2 ^ s / (2 ^ s - 1) := by
      have : 1 - r = (2 ^ s - 1) / 2 ^ s := by
        rw [div_eq_mul_inv, ENNReal.sub_mul (fun _ _ => ENNReal.inv_ne_top.mpr h2s0),
          ENNReal.mul_inv_cancel h2s0 h2st, one_mul, hrinv]
      rw [this, ENNReal.inv_div (Or.inl h2st) (Or.inl h2s0)]
    calc M * c₁ * (2 ^ (d / p) * (c0 ^ s * ∑ j ∈ Finset.range (k - m), r ^ j)) ^ p
        ≤ M * c₁ * (2 ^ (d / p) * (c0 ^ s * (1 - r)⁻¹)) ^ p := by gcongr
      _ = 2 ^ d * M * c₁ * (2 * (ε₀ : ℝ≥0∞) * 2⁻¹ ^ m) ^ (q - d) / (2 ^ s - 1) ^ p := by
        rw [h1r, mul_assoc 2 (ε₀ : ℝ≥0∞), ← hc0def,
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
          ENNReal.div_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ q - d)]
        have e1 : d / p * p = d := by field_simp
        have e2 : s * p = q - d := by rw [hs]; field_simp
        rw [e1, e2]
        simp only [div_eq_mul_inv]
        ring

end SecondTerm

end ProbabilityTheory
