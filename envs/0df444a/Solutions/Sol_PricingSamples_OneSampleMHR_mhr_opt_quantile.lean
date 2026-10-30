-- Prove2me | solution 1 for PricingSamples.OneSampleMHR.mhr_opt_quantile
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:55:01.442686+00:00
-- url     : https://prove2.me/submissions/be3912f6-1257-4676-a3b4-5d3f5b4d37a7

import Mathlib
import Definitions.Def_PricingSamples_OneSampleMHR_Setting

open MeasureTheory PricingSamples.OneSampleMHR

theorem solution (μ : Measure ℝ) (hF : InFAlpha 1 μ) (r : ℝ) (hr : IsOptPrice μ r) :
    Real.exp (-1) ≤ ccdf μ r := by
  obtain ⟨⟨hprob, hneg, -, -⟩, hac, hconv⟩ := hF
  have hIic : μ (Set.Iic 0) = 0 := by
    rw [← Set.Iio_insert]
    refine le_antisymm ?_ (zero_le)
    calc μ (insert 0 (Set.Iio 0)) ≤ μ {0} + μ (Set.Iio 0) := by
          rw [Set.insert_eq]; exact measure_union_le _ _
      _ = 0 := by rw [hneg, hac (Real.volume_singleton)]; simp
  have hIoi : μ (Set.Ioi 0) = 1 := by
    rw [← Set.compl_Iic, prob_compl_eq_one_iff measurableSet_Iic]; exact hIic
  have h0 : ccdf μ 0 = 1 := by simp [ccdf, hIoi]
  have hnn : ∀ p, 0 ≤ ccdf μ p := fun p => ENNReal.toReal_nonneg
  rcases hr with ⟨hr0, hmax⟩
  rcases hr0.eq_or_lt with h | hrpos
  · rw [← h, h0]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hmax' : ∀ p, 0 ≤ p → p * ccdf μ p ≤ r * ccdf μ r := fun p hp => hmax (Set.mem_Ici.mpr hp)
  have hqr : 0 < ccdf μ r := by
    by_contra hle
    have hz : ccdf μ r = 0 := le_antisymm (not_lt.mp hle) (hnn r)
    have hp : ∀ n : ℕ, μ (Set.Ioi (1 / ((n:ℝ) + 1))) = 0 := by
      intro n
      have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      have h1 := hmax' _ hpos.le
      rw [hz, mul_zero] at h1
      have h2 : ccdf μ (1 / ((n:ℝ) + 1)) = 0 :=
        le_antisymm (by
          by_contra h3
          push Not at h3
          have := mul_pos hpos h3
          linarith) (hnn _)
      unfold ccdf at h2
      rcases (ENNReal.toReal_eq_zero_iff _).mp h2 with h4 | h4
      · exact h4
      · exact absurd h4 (measure_ne_top μ _)
    have hU : Set.Ioi (0:ℝ) = ⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1)) := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩
        exact lt_trans (by positivity) hn
    have : μ (Set.Ioi (0:ℝ)) = 0 := by rw [hU]; exact measure_iUnion_null hp
    rw [hIoi] at this
    exact one_ne_zero this
  set h := -Real.log (ccdf μ r) with hh
  have hq_eq : ccdf μ r = Real.exp (-h) := by rw [hh, neg_neg, Real.exp_log hqr]
  have hS0 : (0:ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} := ⟨le_rfl, by rw [h0]; norm_num⟩
  have hSr : r ∈ {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v} := ⟨hrpos.le, hqr⟩
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Real.exp (-(t * h)) ≤ ccdf μ (t * r) := by
    intro t ht0 ht1
    have hmem := hconv.1 hS0 hSr (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    have hineq := hconv.2 hS0 hSr (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, GammaAInv, if_true, h0, Real.log_one,
      neg_zero] at hineq hmem
    have hpos : 0 < ccdf μ (t * r) := hmem.2
    have : -(t * h) ≤ Real.log (ccdf μ (t * r)) := by rw [hh]; linarith
    calc Real.exp (-(t * h)) ≤ Real.exp (Real.log (ccdf μ (t * r))) := Real.exp_le_exp.mpr this
      _ = ccdf μ (t * r) := Real.exp_log hpos
  have hh1 : h ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hhpos : 0 < h := by linarith
    have ht0 : 0 ≤ 1 / h := by positivity
    have ht1 : 1 / h ≤ 1 := by rw [div_le_one hhpos]; exact hgt.le
    have k := key (1 / h) ht0 ht1
    have e1 : 1 / h * h = 1 := by field_simp
    rw [e1] at k
    have opt := hmax' (1 / h * r) (by positivity)
    have : 1 / h * r * Real.exp (-1) ≤ r * Real.exp (-h) := by
      rw [← hq_eq]
      calc 1 / h * r * Real.exp (-1) ≤ 1 / h * r * ccdf μ (1 / h * r) := by
            apply mul_le_mul_of_nonneg_left k; positivity
        _ ≤ r * ccdf μ r := opt
    have h2 : Real.exp (-1) ≤ h * Real.exp (-h) := by
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ h / r)
      have e2 : h / r * (1 / h * r * Real.exp (-1)) = Real.exp (-1) := by field_simp
      have e3 : h / r * (r * Real.exp (-h)) = h * Real.exp (-h) := by field_simp
      linarith
    have h3 : h < Real.exp (h - 1) := by
      have := Real.add_one_lt_exp (by linarith : h - 1 ≠ 0)
      linarith
    have e4 : Real.exp (-1) = Real.exp (h - 1) * Real.exp (-h) := by
      rw [← Real.exp_add]; ring_nf
    rw [e4] at h2
    have := (mul_le_mul_iff_left₀ (Real.exp_pos (-h))).mp h2
    linarith
  rw [hq_eq]
  exact Real.exp_le_exp.mpr (by linarith)
