-- Prove2me | solution 1 for ShiQMAConstructiveSchedule.eval_le_pow_budget
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T12:59:17.028494+00:00
-- url     : https://prove2.me/submissions/b2b800c0-ef8b-4cda-ab1d-8468c05d119c

import Definitions.Def_ShiQMAConstructiveSchedule
import Theorems.Thm_ShiQMAPolynomialBound_eval_le_coeffSum_mul

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem solution (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ 2 ^ exponentBudget p n := by
  let A := Nat.log 2 (p.eval 1 + 1) + 1
  let B := Nat.log 2 (n + 1) + 1
  have hc : p.eval 1 ≤ 2 ^ A := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
      (p.eval 1 + 1)
    dsimp [A]
    omega
  have hn : n + 1 ≤ 2 ^ B := by
    exact Nat.le_of_lt
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 1))
  have hpow : (n + 1) ^ p.natDegree ≤
      (2 ^ B) ^ p.natDegree :=
    Nat.pow_le_pow_left hn p.natDegree
  calc
    p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree :=
      ShiQMAPolynomialBound.eval_le_coeffSum_mul p n
    _ ≤ 2 ^ A * (2 ^ B) ^ p.natDegree :=
      Nat.mul_le_mul hc hpow
    _ = 2 ^ exponentBudget p n := by
      have hpoweq : (2 ^ B) ^ p.natDegree =
          2 ^ (B * p.natDegree) :=
        (pow_mul 2 B p.natDegree).symm
      rw [hpoweq, ← pow_add]
      congr 1
      dsimp [exponentBudget, A, B]
      ring
