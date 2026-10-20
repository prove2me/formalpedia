-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P08.fixedStrengthGain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:40:48.168589+00:00
-- url     : https://prove2.me/submissions/5c0dbf8c-9bb2-4156-b67a-fbc86c02fd5b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

lemma g53_logs :
    (0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808) ∧
    (1.0986122 < Real.log 3 ∧ Real.log 3 < 1.0986123) ∧
    (1.6094379 < Real.log 5 ∧ Real.log 5 < 1.6094380) := by
  set L2 := Real.log 2
  set L3 := Real.log 3
  set L5 := Real.log 5
  have a1 := Real.log_two_gt_d9
  have a2 := Real.log_two_lt_d9
  have s1 := Real.abs_log_sub_add_sum_range_le (x := 1/9) (by norm_num) 10
  have e1 : Real.log (1 - 1/9) = 3 * L2 - 2 * L3 := by
    rw [show (1 : ℝ) - 1/9 = 2^3 / 3^2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have s2 := Real.abs_log_sub_add_sum_range_le (x := 1/25) (by norm_num) 8
  have e2 : Real.log (1 - 1/25) = 3 * L2 + L3 - 2 * L5 := by
    rw [show (1 : ℝ) - 1/25 = (2^3 * 3) / 5^2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [e1] at s1
  rw [e2] at s2
  norm_num [Finset.sum_range_succ] at s1 s2
  rw [abs_le] at s1 s2
  obtain ⟨s1a, s1b⟩ := s1
  obtain ⟨s2a, s2b⟩ := s2
  refine ⟨⟨a1, a2⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma g53_ent_num :
    Real.binEntropy ((10 + Real.sqrt 73) / 20) <
      Real.binEntropy (1/4) - Real.binEntropy (7/10) + Real.binEntropy (9/10) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := g53_logs
  have hs : (8.544 : ℝ) ≤ Real.sqrt 73 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2 : Real.sqrt 73 ≤ 10 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hmono : Real.binEntropy ((10 + Real.sqrt 73) / 20) ≤ Real.binEntropy (37/40) := by
    apply Real.binEntropy_strictAntiOn.antitoneOn
    · constructor <;> norm_num
    · constructor <;> linarith
    · linarith
  refine lt_of_le_of_lt hmono ?_
  simp only [Real.binEntropy]
  norm_num
  -- log 37 lower bound, log 7 upper bound
  have h37 : Real.log 37 = 2 * Real.log 2 + 2 * Real.log 3 + Real.log (37/36) := by
    rw [show (37:ℝ) = 2^2 * 3^2 * (37/36) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have l37 := Real.one_sub_inv_le_log_of_pos (x := 37/36) (by norm_num)
  have h7 : 2 * Real.log 7 = Real.log 2 + 2 * Real.log 5 + Real.log (49/50) := by
    rw [show Real.log (49/50) = Real.log 49 - Real.log 50 from Real.log_div (by norm_num) (by norm_num),
      show (49:ℝ) = 7^2 by norm_num, show (50:ℝ) = 2 * 5^2 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have l7 := Real.one_sub_inv_le_log_of_pos (x := 49/50) (by norm_num)
  have L4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have L10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10:ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have L40 : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    rw [show (40:ℝ) = 2^3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have L9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]; push_cast; ring
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), L4, L10, L40, L9]
  norm_num at l37 l7 a1 a2 b1 b2 c1 c2
  linarith

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P08
open scoped Matrix ComplexConjugate ComplexOrder
noncomputable section
attribute [local instance] Classical.propDecidable

theorem solution :
    twoRoundRate (1 / 2) (4 / 5) =
      1 - binEntropy2 (7 / 10) + binEntropy2 (9 / 10) - binEntropy2 ((10 + Real.sqrt 73) / 20) ∧
    1 - binEntropy2 (1 / 4) < twoRoundRate (1 / 2) (4 / 5) := by
  have hrate : twoRoundRate (1 / 2) (4 / 5) =
      1 - binEntropy2 (7 / 10) + binEntropy2 (9 / 10) - binEntropy2 ((10 + Real.sqrt 73) / 20) := by
    unfold twoRoundRate
    have hsq : Real.sqrt ((1 - 1/2 : ℝ) ^ 2 + (1 - (1 - 1/2) ^ 2) * (4/5) ^ 2) = Real.sqrt 73 / 10 := by
      rw [show ((1 - 1/2 : ℝ) ^ 2 + (1 - (1 - 1/2) ^ 2) * (4/5) ^ 2) = 73 / 10^2 by norm_num,
        Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num)]
    rw [hsq, show (1 + √73 / 10) / 2 = (10 + √73) / 20 by ring]
    norm_num
  refine ⟨hrate, ?_⟩
  rw [hrate]
  unfold binEntropy2
  have hl := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have := g53_ent_num
  have key : Real.binEntropy ((10 + Real.sqrt 73) / 20) / Real.log 2 <
      (Real.binEntropy (1/4) - Real.binEntropy (7/10) + Real.binEntropy (9/10)) / Real.log 2 :=
    div_lt_div_of_pos_right this hl
  have e : (Real.binEntropy (1/4) - Real.binEntropy (7/10) + Real.binEntropy (9/10)) / Real.log 2 =
      Real.binEntropy (1/4) / Real.log 2 - Real.binEntropy (7/10) / Real.log 2 + Real.binEntropy (9/10) / Real.log 2 := by ring
  linarith
