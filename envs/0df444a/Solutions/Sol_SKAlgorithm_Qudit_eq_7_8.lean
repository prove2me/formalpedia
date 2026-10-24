-- Prove2me | solution 1 for SKAlgorithm.Qudit.eq_7_8
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:49:21.308025+00:00
-- url     : https://prove2.me/submissions/3ab9ba91-3ad8-4a21-a996-18ce7db9a5fa

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open Real

namespace SKAlgorithm.Qudit.RateProof

lemma geometric_power_identity (n : ℕ) :
    (((3 : ℝ) / 2) ^ n) ^ (Real.log 5 / Real.log (3 / 2)) = (5 : ℝ) ^ n := by
  have hb : (0 : ℝ) < 3 / 2 := by norm_num
  have hl : Real.log ((3 : ℝ) / 2) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : ((3 : ℝ) / 2) ^ (Real.log 5 / Real.log (3 / 2)) = 5 := by
    apply (Real.mul_log_eq_log_iff hb (by norm_num : (0 : ℝ) < 5)).mp
    exact div_mul_cancel₀ _ hl
  rw [← Real.rpow_natCast_mul hb.le, mul_comm (n : ℝ), Real.rpow_mul_natCast hb.le, he]

end SKAlgorithm.Qudit.RateProof

open SKAlgorithm.Qudit.RateProof

theorem solution (c ε₀ : ℝ) (hc : 0 < c) (hε₀ : 0 < ε₀)
    (hlt : ε₀ * c ^ 2 < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      1 / c ^ 2 * (ε₀ * c ^ 2) ^ (((3 : ℝ) / 2) ^ n) < ε ∧
      (5 : ℝ) ^ n ≤ K * Real.log (2 + 1 / ε) ^ (Real.log 5 / Real.log (3 / 2)) := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hb : 0 < ε₀ * c ^ 2 := mul_pos hε₀ hc2
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let a := -Real.log (ε₀ * c ^ 2)
  let B := |Real.log (c ^ 2)|
  let C := 1 / a + (1 + B / a) / Real.log 2
  let p := Real.log 5 / Real.log ((3 : ℝ) / 2)
  have ha : 0 < a := neg_pos.mpr (Real.log_neg hb hlt)
  have hB : 0 ≤ B := abs_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  have hp : 0 < p := div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  refine ⟨((3 / 2 : ℝ) * C) ^ p, Real.rpow_pos_of_pos (mul_pos (by norm_num) hC) _, ?_⟩
  intro ε hε
  let L := Real.log (2 + 1 / ε)
  have hL2 : Real.log (2 : ℝ) ≤ L :=
    Real.log_le_log (by norm_num) (by have := one_div_pos.mpr hε; linarith)
  have hL : 0 < L := lt_of_lt_of_le hl2 hL2
  have hrat : 1 ≤ L / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hL2)
  let T := 1 + (L + B) / a
  have hT : 1 ≤ T := by
    exact le_add_of_nonneg_right (div_nonneg (add_nonneg hL.le hB) ha.le)
  have hTC : T ≤ C * L := by
    have hh := mul_le_mul_of_nonneg_left hrat (show 0 ≤ 1 + B / a by positivity)
    calc
      T = L / a + (1 + B / a) * 1 := by dsimp [T]; ring
      _ ≤ L / a + (1 + B / a) * (L / Real.log 2) := add_le_add le_rfl hh
      _ = C * L := by dsimp [C]; ring
  obtain ⟨m, hm, hm'⟩ := exists_nat_pow_near hT (by norm_num : (1 : ℝ) < 3 / 2)
  refine ⟨m + 1, ?_, ?_⟩
  · have hthreshold : (L + B) / a < ((3 : ℝ) / 2) ^ (m + 1) := by
      dsimp [T] at hm'
      linarith
    have hprod : L + B < a * ((3 : ℝ) / 2) ^ (m + 1) :=
      by simpa only [mul_comm] using (div_lt_iff₀ ha).mp hthreshold
    have hlogε : -Real.log ε < L := by
      have hh := Real.log_lt_log (one_div_pos.mpr hε)
        (show 1 / ε < 2 + 1 / ε by linarith)
      simpa only [Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub] using hh
    have hpos : 0 < 1 / c ^ 2 * (ε₀ * c ^ 2) ^ (((3 : ℝ) / 2) ^ (m + 1)) :=
      mul_pos (one_div_pos.mpr hc2) (Real.rpow_pos_of_pos hb _)
    apply (Real.log_lt_log_iff hpos hε).mp
    rw [Real.log_mul (ne_of_gt (one_div_pos.mpr hc2))
      (ne_of_gt (Real.rpow_pos_of_pos hb _)), Real.log_div one_ne_zero hc2.ne', Real.log_one,
      zero_sub, Real.log_rpow hb]
    dsimp [a, B] at hprod
    nlinarith [neg_le_abs (Real.log (c ^ 2))]
  · have hscale : ((3 : ℝ) / 2) ^ (m + 1) ≤ ((3 : ℝ) / 2 * C) * L := by
      rw [pow_succ]
      calc
        _ ≤ T * (3 / 2) := mul_le_mul_of_nonneg_right hm (by norm_num)
        _ ≤ (C * L) * (3 / 2) := mul_le_mul_of_nonneg_right hTC (by norm_num)
        _ = _ := by ring
    calc
      _ = (((3 : ℝ) / 2) ^ (m + 1)) ^ p := (geometric_power_identity _).symm
      _ ≤ (((3 : ℝ) / 2 * C) * L) ^ p := Real.rpow_le_rpow (by positivity) hscale hp.le
      _ = (((3 : ℝ) / 2) * C) ^ p * L ^ p := Real.mul_rpow (by positivity) hL.le
