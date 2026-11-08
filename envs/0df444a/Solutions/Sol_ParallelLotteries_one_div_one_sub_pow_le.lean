-- Prove2me | solution 1 for ParallelLotteries.one_div_one_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:42:41.594888+00:00
-- url     : https://prove2.me/submissions/e1df72ed-ada0-4dc2-b85d-289e50b117b2

import Mathlib

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    1 / (1 - (1 - 1 / (k : ℝ)) ^ k) ≤ 2 - 1 / (k : ℝ) ∧
    (2 ≤ k → 1 / (1 - (1 - 1 / (k : ℝ)) ^ k) < 2 - 1 / (k : ℝ)) := by
  have main : 2 ≤ k → 1 / (1 - (1 - 1 / (k : ℝ)) ^ k) < 2 - 1 / (k : ℝ) := by
    intro hk2
    have hkr : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    have hkpos : (0:ℝ) < (k:ℝ) := by linarith
    have hinv : 1 / (k:ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hkpos (by norm_num)]
      linarith
    have hinvpos : 0 < 1 / (k:ℝ) := by positivity
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - 1 / (k:ℝ) := ⟨_, rfl⟩
    have e2 : (2:ℝ) - 1 / (k:ℝ) = 1 + q := by rw [hq]; ring
    rw [← hq, e2]
    have hq0 : 0 < q := by rw [hq]; linarith
    have hq1 : q < 1 := by rw [hq]; linarith
    have hA : q ≤ Real.exp (-(1 / (k:ℝ))) := by
      have := Real.add_one_le_exp (-(1 / (k:ℝ)))
      rw [hq]
      linarith
    have hmul : ((k:ℝ) - 1) * (-(1 / (k:ℝ))) = -q := by
      rw [mul_neg, neg_inj, sub_mul, one_mul, mul_one_div_cancel hkpos.ne', hq]
    have hB : q ^ (k - 1) ≤ Real.exp (-q) := by
      calc q ^ (k - 1) ≤ (Real.exp (-(1 / (k:ℝ)))) ^ (k - 1) := pow_le_pow_left₀ hq0.le hA _
        _ = Real.exp (((k - 1 : ℕ) : ℝ) * (-(1 / (k:ℝ)))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-q) := by
          rw [Nat.cast_sub (by omega), Nat.cast_one, hmul]
    have hC : 1 + q < Real.exp q := by
      have := Real.add_one_lt_exp hq0.ne'
      linarith
    have hD : q ^ (k - 1) * (1 + q) < 1 := by
      calc q ^ (k - 1) * (1 + q) ≤ Real.exp (-q) * (1 + q) :=
            mul_le_mul_of_nonneg_right hB (by linarith)
        _ < Real.exp (-q) * Real.exp q := mul_lt_mul_of_pos_left hC (Real.exp_pos _)
        _ = 1 := by rw [← Real.exp_add]; simp
    have hk' : q ^ k = q ^ (k - 1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    have hP := pow_pos hq0 (k - 1)
    have hpos : 0 < 1 - q ^ k := by
      rw [hk']
      nlinarith
    rw [div_lt_iff₀ hpos, hk']
    nlinarith [mul_lt_mul_of_pos_right hD hq0]
  refine ⟨?_, main⟩
  rcases eq_or_lt_of_le hk with h | h
  · subst h
    norm_num
  · exact (main (by omega)).le
