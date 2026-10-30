-- Prove2me | solution 1 for WilliamsonShmoys.choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:54.385043+00:00
-- url     : https://prove2.me/submissions/9961b095-17bc-46c5-a1b6-120f5b5b6e59

import Mathlib

set_option autoImplicit false

theorem solution
    (n : Nat)
    (hcard : 3 <= n)
    (hedges : n.choose 2 <= 3 * n - 6) :
    n <= 4 := by
  by_contra h
  have hn5 : 5 <= n := by omega
  have hchoose : 2 * n.choose 2 = n * (n - 1) := by
    calc
      2 * n.choose 2 = (n * (n - 1) / 2) * 2 := by
        rw [Nat.choose_two_right]
        omega
      _ = 2 * (n * (n - 1) / 2) := Nat.mul_comm _ _
      _ = n * (n - 1) :=
        Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have hprod : n * (n - 1) <= 2 * (3 * n - 6) := by
    calc
      n * (n - 1) = 2 * n.choose 2 := hchoose.symm
      _ <= 2 * (3 * n - 6) := Nat.mul_le_mul_left 2 hedges
  let m : Nat := n - 5
  have hn : n = m + 5 := by
    dsimp [m]
    omega
  have hminus : (m + 5) - 1 = m + 4 := by omega
  have hsub : 3 * (m + 5) - 6 = 3 * m + 9 := by omega
  rw [hn, hminus, hsub] at hprod
  nlinarith [hprod]