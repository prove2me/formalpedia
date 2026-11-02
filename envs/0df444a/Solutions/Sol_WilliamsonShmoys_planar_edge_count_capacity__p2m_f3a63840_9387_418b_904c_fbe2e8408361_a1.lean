-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_capacity__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:39:50.623528+00:00
-- url     : https://prove2.me/submissions/4c64997b-6b02-4f54-acbc-aaa38f8e8cdb

import Mathlib

set_option autoImplicit false

theorem solution (n : Nat) (hn : 3 ≤ n) :
    3 * n - 6 ≤ n * (n - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
  by_cases h4 : n < 4
  · have hn3 : n = 3 := by omega
    subst n
    norm_num
  · have hn4 : 4 ≤ n := by omega
    have hsub1 : n - 1 + 1 = n := by omega
    have hsub3 : n - 3 + 3 = n := by omega
    have hsub4 : n - 4 + 4 = n := by omega
    have hsub6 : 3 * n - 6 + 6 = 3 * n := by omega
    have hprod : 0 ≤ (n - 3) * (n - 4) := Nat.zero_le _
    nlinarith