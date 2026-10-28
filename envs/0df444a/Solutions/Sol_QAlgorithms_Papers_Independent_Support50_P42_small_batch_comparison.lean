-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.small_batch_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:55:51.369894+00:00
-- url     : https://prove2.me/submissions/2581993b-939f-4234-af9d-6187627b9e5a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace X4P42
open QAlgorithms.Papers.Independent.Support50.P42

lemma l3 : 0 < Real.logb 2 3 ∧ Real.logb 2 3 < 1.6 := by
  refine ⟨Real.logb_pos (by norm_num) (by norm_num), ?_⟩
  have h : (5 : ℝ) * Real.logb 2 3 < 8 := by
    have e1 : (5 : ℝ) * Real.logb 2 3 = Real.logb 2 243 := by
      rw [show (243 : ℝ) = 3 ^ (5 : ℕ) by norm_num, Real.logb_pow]; norm_num
    have e2 : Real.logb 2 (256 : ℝ) = 8 := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [e1, ← e2]
    exact Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  linarith

lemma l2 : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
lemma l4 : Real.logb 2 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, l2]; norm_num
lemma l6 : Real.logb 2 6 = 1 + Real.logb 2 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.logb_mul (by norm_num) (by norm_num), l2]

theorem main (n : ℕ) (hn : 1 ≤ n) (hn5 : n < 5) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    projectedYield n p / (n : ℝ) < procrusteanYield p := by
  obtain ⟨a0, a1⟩ := l3
  have hq : 0 < 1 - p := by linarith
  unfold procrusteanYield
  rcases le_total p (1 - p) with h | h
  · rw [min_eq_left h]
    interval_cases n <;>
      simp [projectedYield, schmidtOutcomeWeight, Finset.sum_range_succ, Nat.choose, l4, l6]
    · exact hp
    · nlinarith [mul_pos hp hq]
    · nlinarith [mul_pos (mul_pos hp hq) (by linarith : (0:ℝ) < 2 - Real.logb 2 3), mul_pos hp hq,
        mul_pos (mul_pos hp hq) a0]
    · nlinarith [mul_pos (mul_pos (pow_pos hp 2) (pow_pos hq 2)) (by linarith : (0:ℝ) < 1.6 - Real.logb 2 3),
        mul_pos hp hq, pow_pos hp 3, mul_pos (pow_pos hp 2) hq, mul_pos hp (pow_pos hq 2)]
  · rw [min_eq_right h]
    interval_cases n <;>
      simp [projectedYield, schmidtOutcomeWeight, Finset.sum_range_succ, Nat.choose, l4, l6]
    · exact hp1
    · nlinarith [mul_pos hp hq]
    · nlinarith [mul_pos (mul_pos hp hq) (by linarith : (0:ℝ) < 2 - Real.logb 2 3), mul_pos hp hq,
        mul_pos (mul_pos hp hq) a0]
    · nlinarith [mul_pos (mul_pos (pow_pos hp 2) (pow_pos hq 2)) (by linarith : (0:ℝ) < 1.6 - Real.logb 2 3),
        mul_pos hp hq, pow_pos hq 3, mul_pos (pow_pos hq 2) hp, mul_pos hq (pow_pos hp 2)]

end X4P42

theorem solution (n : ℕ) (hn : 1≤n) (hn5 : n<5)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    QAlgorithms.Papers.Independent.Support50.P42.projectedYield n p/(n : ℝ) <
      QAlgorithms.Papers.Independent.Support50.P42.procrusteanYield p :=
  X4P42.main n hn hn5 p hp hp1

#print axioms solution
