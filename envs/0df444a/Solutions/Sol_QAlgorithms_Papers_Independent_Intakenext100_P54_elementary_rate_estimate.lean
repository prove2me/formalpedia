-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P54.elementary_rate_estimate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:26:36.132707+00:00
-- url     : https://prove2.me/submissions/e7adab5f-7634-4541-bfac-b8ccea423047

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

open QAlgorithms.Papers.Independent.Intakenext100.P54 in
theorem solution (xi : ℝ) (hLower : -1 ≤ xi) (hUpper : xi ≤ 1) :
    ((xi ^ 2 / (12 * Real.log 2) : ℝ) : EReal) ≤ elementaryRate xi := by
  unfold elementaryRate
  by_cases hxi : xi = -1
  · rw [if_pos hxi]
    exact le_top
  · rw [if_neg hxi]
    have hgt : -1 < xi := lt_of_le_of_ne hLower (Ne.symm hxi)
    obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (1 + xi) := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr (by linarith)
    have hs2 : s ^ 2 = 1 + xi := by rw [hsdef]; exact Real.sq_sqrt (by linarith)
    have hlog : Real.log (1 + xi) = 2 * Real.log s := by
      rw [hsdef, Real.log_sqrt (by linarith)]
      ring
    have hle : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
    have hs32 : s ≤ 3 / 2 := by nlinarith
    have h6 : 0 ≤ 6 - (s + 1) ^ 2 := by nlinarith
    have hprod := mul_nonneg (sq_nonneg (s - 1)) h6
    have hid : xi - 2 * (s - 1) - xi ^ 2 / 6 = (s - 1) ^ 2 * (6 - (s + 1) ^ 2) / 6 := by
      rw [show xi = s ^ 2 - 1 by linarith]
      ring
    have key : xi ^ 2 / 6 ≤ xi - Real.log (1 + xi) := by
      rw [hlog]
      linarith
    have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [EReal.coe_le_coe_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr key) hL.le]
