-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P22.thermal_entropy_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:08:56.624713+00:00
-- url     : https://prove2.me/submissions/dcaef47f-f2cd-424c-ae48-2570844fc617

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P22
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy thermalEntropy)

theorem s110_0946_logbd {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * x ^ 3 ∧
    |Real.log (1 - x) - (-x - x ^ 2 / 2)| ≤ 2 * x ^ 3 := by
  have hax : |x| = x := abs_of_pos hx0
  have hlt : |x| < 1 := by rw [hax]; linarith
  have hlt' : |-x| < 1 := by rw [abs_neg, hax]; linarith
  have h1 := Real.abs_log_sub_add_sum_range_le hlt 2
  have h2 := Real.abs_log_sub_add_sum_range_le hlt' 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, hax] at h1 h2
  have hden : x ^ (2 + 1) / (1 - x) ≤ 2 * x ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 < x ^ 3 := by positivity
    norm_num; nlinarith
  constructor
  · refine le_trans (le_of_eq ?_) (h2.trans hden)
    congr 1; push_cast; ring_nf
  · refine le_trans (le_of_eq ?_) (h1.trans hden)
    congr 1; push_cast; ring_nf

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℝ, 1 ≤ N ∧ ∀ nu : ℝ, N ≤ nu →
      |symplecticEntropy nu - (Real.log (nu / 2) + 1)| ≤ C / nu ^ 2 := by
  refine ⟨4, by norm_num, 2, by norm_num, fun nu hnu => ?_⟩
  have hnu0 : 0 < nu := by linarith
  set t := 1 / nu with ht
  have ht0 : 0 < t := by positivity
  have hth : t ≤ 1 / 2 := by
    rw [ht, div_le_div_iff₀ hnu0 (by norm_num)]; linarith
  have hnt : nu * t = 1 := by rw [ht]; field_simp
  clear_value t
  obtain ⟨b1, b2⟩ := s110_0946_logbd ht0 hth
  have hA : Real.log ((nu + 1) / 2) = Real.log (nu / 2) + Real.log (1 + t) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; rw [ht]; field_simp
  have hB : Real.log ((nu - 1) / 2) = Real.log (nu / 2) + Real.log (1 - t) := by
    rw [← Real.log_mul (by positivity) (by linarith)]
    congr 1; rw [ht]; field_simp
  have hS : symplecticEntropy nu - (Real.log (nu / 2) + 1) =
      nu / 2 * ((Real.log (1 + t) - (t - t ^ 2 / 2)) - (Real.log (1 - t) - (-t - t ^ 2 / 2)))
      - t ^ 2 / 2 + ((Real.log (1 + t) - (t - t ^ 2 / 2)) +
        (Real.log (1 - t) - (-t - t ^ 2 / 2))) / 2 := by
    simp only [symplecticEntropy, thermalEntropy]
    have e1 : (nu - 1) / 2 + 1 = (nu + 1) / 2 := by ring
    rw [e1, hA, hB]
    have : nu / 2 * (2 * t) = 1 := by linarith
    linear_combination this
  rw [hS]
  set e1 := Real.log (1 + t) - (t - t ^ 2 / 2)
  set e2 := Real.log (1 - t) - (-t - t ^ 2 / 2)
  have hC : 4 / nu ^ 2 = 4 * t ^ 2 := by rw [ht]; field_simp
  rw [hC]
  have hnt3 : nu * t ^ 3 = t ^ 2 := by
    have : nu * t ^ 3 = (nu * t) * t ^ 2 := by ring
    rw [this, hnt, one_mul]
  have hd : |nu / 2 * (e1 - e2)| ≤ 2 * t ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < nu / 2)]
    calc nu / 2 * |e1 - e2| ≤ nu / 2 * (2 * t ^ 3 + 2 * t ^ 3) := by
          gcongr; exact (abs_sub _ _).trans (add_le_add b1 b2)
      _ = 2 * (nu * t ^ 3) := by ring
      _ = 2 * t ^ 2 := by rw [hnt3]
  have hs : |(e1 + e2) / 2| ≤ 2 * t ^ 3 := by
    rw [abs_div, abs_two]
    have := (abs_add_le e1 e2).trans (add_le_add b1 b2)
    linarith
  have ht3 : t ^ 3 ≤ t ^ 2 / 2 := by
    have : t ^ 3 = t * t ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg t]
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  rw [abs_le] at hd hs ⊢
  constructor <;> nlinarith
