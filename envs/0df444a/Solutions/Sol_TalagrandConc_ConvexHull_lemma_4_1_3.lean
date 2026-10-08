-- Prove2me | solution 1 for TalagrandConc.ConvexHull.lemma_4_1_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:39:32.522096+00:00
-- url     : https://prove2.me/submissions/12410273-294a-42eb-92f5-3342b2fd8052

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic



namespace TalagrandConc.ConvexHull

open scoped ENNReal

/-- Taylor bound: `exp v ≤ 1 + v + v^2/2 + v^3/6 + 5 v^4/96` for `0 ≤ v ≤ 1`. -/
lemma exp_upper4 (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    Real.exp v ≤ 1 + v + v ^ 2 / 2 + v ^ 3 / 6 + 5 * v ^ 4 / 96 := by
  have h := Real.exp_bound (x := v) (by rw [abs_of_nonneg h0]; exact h1) (n := 4) (by norm_num)
  rw [abs_of_nonneg h0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  nlinarith

/-- Taylor bound: `exp (-u) ≤ 1 - u + u^2/2 - u^3/6 + u^4/24 + u^5/100` for `0 ≤ u ≤ 1`. -/
lemma exp_neg_upper5 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 100 := by
  have h := Real.exp_bound (x := -u) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 5) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  nlinarith

lemma key_real (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    Real.exp (u - u ^ 2) ≤ 2 - Real.exp (-u) := by
  have hv0 : 0 ≤ u - u ^ 2 := by nlinarith
  have hv1 : u - u ^ 2 ≤ 1 := by nlinarith
  have hA := exp_upper4 (u - u ^ 2) hv0 hv1
  have hB := exp_neg_upper5 u h0 (by linarith)
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith
  have hu3 : u ^ 3 ≤ 1 / 8 := by nlinarith
  have hu4 : u ^ 4 ≤ 1 / 16 := by nlinarith
  have hu5 : u ^ 5 ≤ 1 / 32 := by nlinarith
  have hbr : 0 ≤ 2400 - 225 * u - 724 * u ^ 2 - 350 * u ^ 3 + 500 * u ^ 4 - 125 * u ^ 5 := by
    nlinarith
  have hu3' : 0 ≤ u ^ 3 := by positivity
  have hd : 0 ≤ u ^ 3 * (2400 - 225 * u - 724 * u ^ 2 - 350 * u ^ 3 + 500 * u ^ 4 - 125 * u ^ 5) :=
    mul_nonneg hu3' hbr
  nlinarith

lemma lemma_4_1_3_core (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (⨅ l ∈ Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal r ^ (-l) * ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4)))
      ≤ ENNReal.ofReal (2 - r) := by
  rcases le_or_gt r (Real.exp (-1 / 2)) with hsmall | hbig
  · -- take l = 0
    refine (iInf₂_le (0 : ℝ) ⟨le_rfl, zero_le_one⟩).trans ?_
    rw [neg_zero, ENNReal.rpow_zero, one_mul]
    apply ENNReal.ofReal_le_ofReal
    have e1 : Real.exp (1 / 4) ≤ 4 / 3 := by
      have h := Real.add_one_le_exp (-1 / 4)
      have h2 : Real.exp (1 / 4) * Real.exp (-1 / 4) = 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 4)]
    have e2 : Real.exp (-1 / 2) ≤ 2 / 3 := by
      have h := Real.add_one_le_exp (1 / 2)
      have h2 : Real.exp (1 / 2) * Real.exp (-1 / 2) = 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (-1 / 2)]
    norm_num
    linarith
  · -- take l = 1 + 2 log r
    have hrpos : 0 < r := lt_of_le_of_lt (Real.exp_pos _).le hbig
    have hlog_le : Real.log r ≤ 0 := Real.log_nonpos hr0 hr1
    have hlog_gt : -1 / 2 < Real.log r := by
      have := Real.log_lt_log (Real.exp_pos _) hbig
      rwa [Real.log_exp] at this
    set l : ℝ := 1 + 2 * Real.log r with hl
    have hl0 : 0 ≤ l := by rw [hl]; linarith
    have hl1 : l ≤ 1 := by rw [hl]; linarith
    refine (iInf₂_le l ⟨hl0, hl1⟩).trans ?_
    rw [ENNReal.ofReal_rpow_of_pos hrpos, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr0 _)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_def_of_pos hrpos, ← Real.exp_add]
    set u : ℝ := -Real.log r with hu
    have hu0 : 0 ≤ u := by rw [hu]; linarith
    have hu1 : u ≤ 1 / 2 := by rw [hu]; linarith
    have hr_eq : r = Real.exp (-u) := by
      rw [hu, neg_neg, Real.exp_log hrpos]
    have harg : Real.log r * -l + (1 - l) ^ 2 / 4 = u - u ^ 2 := by
      rw [hl, hu]; ring
    rw [harg]
    calc Real.exp (u - u ^ 2) ≤ 2 - Real.exp (-u) := key_real u hu0 hu1
      _ = 2 - r := by rw [hr_eq]

end TalagrandConc.ConvexHull

open TalagrandConc.ConvexHull


theorem solution (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (⨅ l ∈ Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal r ^ (-l) * ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4)))
      ≤ ENNReal.ofReal (2 - r) := by
  exact lemma_4_1_3_core r hr0 hr1
