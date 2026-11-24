-- Prove2me | solution 1 for PI.SqfRootsInj.W.sq_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T01:41:51.786833+00:00
-- url     : https://prove2.me/submissions/112d8b6c-10bf-435d-ae48-ce80981754bc

import Mathlib



theorem solution (t : ℝ) (ht0 : 0 ≤ t) (e : ℕ) (he : 1 ≤ e) :
    (e : ℝ) ^ 2 * t ^ e ≤ t * (4 * t) ^ (e - 1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  have aux (j : ℕ) : ((j : ℝ)+1)^2 ≤ (4 : ℝ)^j := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ (4 : ℝ)]; push_cast
      nlinarith [sq_nonneg (j : ℝ), Nat.cast_nonneg (α := ℝ) j]
  rw [Nat.succ_sub_one, mul_pow, pow_succ t]; push_cast
  calc
    _ ≤ (4 : ℝ)^k * (t ^ k * t) := mul_le_mul_of_nonneg_right (aux k) (mul_nonneg (pow_nonneg ht0 _) ht0)
    _ = _ := by ring
