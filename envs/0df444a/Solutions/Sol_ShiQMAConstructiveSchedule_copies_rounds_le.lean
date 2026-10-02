-- Prove2me | solution 1 for ShiQMAConstructiveSchedule.copies_rounds_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T13:08:48.01179+00:00
-- url     : https://prove2.me/submissions/625f742e-43d5-49a9-89a4-fa309ba2317c

import Definitions.Def_ShiQMAConstructiveSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem solution (p : Polynomial ℕ) (n : ℕ) :
    3 ^ rounds p n ≤
      3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4) *
        (n + 1) ^ (2 * p.natDegree) := by
  let A := Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4
  let L := Nat.log 2 (n + 1)
  have hlog : 2 ^ L ≤ n + 1 :=
    Nat.pow_log_le_self 2 (by omega : n + 1 ≠ 0)
  have hbase : 3 ^ L ≤ 4 ^ L :=
    Nat.pow_le_pow_left (by decide : 3 ≤ 4) L
  have hsq : (2 ^ L) ^ 2 ≤ (n + 1) ^ 2 :=
    Nat.pow_le_pow_left hlog 2
  have heq : 4 ^ L = (2 ^ L) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
    exact (pow_mul 2 2 L).symm
  have hunit : 3 ^ L ≤ (n + 1) ^ 2 := by
    rw [heq] at hbase
    exact hbase.trans hsq
  have hpow : (3 ^ L) ^ p.natDegree ≤
      ((n + 1) ^ 2) ^ p.natDegree :=
    Nat.pow_le_pow_left hunit p.natDegree
  have hid : rounds p n = A + L * p.natDegree := by
    dsimp [rounds, exponentBudget, A, L]
    ring
  rw [hid, pow_add, pow_mul]
  change 3 ^ A * (3 ^ L) ^ p.natDegree ≤
    3 ^ A * (n + 1) ^ (2 * p.natDegree)
  rw [pow_mul]
  exact Nat.mul_le_mul_left _ hpow
