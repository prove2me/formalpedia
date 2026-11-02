-- Prove2me | solution 1 for WilliamsonShmoys.three_n_sub_six_le_choose_two__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:42:15.532272+00:00
-- url     : https://prove2.me/submissions/2e3e8df9-3f5c-4aa2-ade6-afc11b92069d

import Mathlib

theorem solution
    (n : Nat) (hn : 3 ≤ n) :
    3 * n - 6 ≤ Nat.choose n 2 := by
  by_cases h : n = 3
  · subst n
    norm_num
  · have hn4 : 4 ≤ n := by omega
    rw [Nat.choose_two_right]
    apply (Nat.le_div_iff_mul_le Nat.two_pos).2
    have h3 : n - 3 + 3 = n := Nat.sub_add_cancel (by omega)
    have h4 : n - 4 + 4 = n := Nat.sub_add_cancel hn4
    have h1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have h6 : 3 * n - 6 + 6 = 3 * n := Nat.sub_add_cancel (by omega)
    have hprod : 0 ≤ (n - 3) * (n - 4) := Nat.zero_le _
    nlinarith
