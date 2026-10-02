-- Prove2me | solution 1 for OddPerfectNumber.Kernel.vp_three_of_mod_one
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T19:53:13.779325+00:00
-- url     : https://prove2.me/submissions/95a2de0c-b38c-4078-8bd1-1faf4766b2d1

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

theorem solution (n : Nat) (hn : n % 3 = 1) :
    (n ^ 2 + n + 1).factorization 3 = 1 := by
  have hn_eq : n = 3 * (n / 3) + 1 := by omega
  set k := n / 3
  have hN : n ^ 2 + n + 1 = 3 * (3 * (k ^ 2 + k) + 1) := by
    rw [hn_eq]
    ring
  rw [hN]
  have h3_pos : (3 : ℕ) ≠ 0 := by decide
  have hm_pos : 3 * (k ^ 2 + k) + 1 ≠ 0 := by omega
  have h_add : (3 * (3 * (k ^ 2 + k) + 1)).factorization 3 =
      (3 : ℕ).factorization 3 + (3 * (k ^ 2 + k) + 1).factorization 3 := by
    rw [Nat.factorization_mul h3_pos hm_pos, Finsupp.add_apply]
  rw [h_add]
  have h3_fact : (3 : ℕ).factorization 3 = 1 :=
    Nat.Prime.factorization_self (by norm_num)
  have hm_fact : (3 * (k ^ 2 + k) + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_remainder (k ^ 2 + k) (by decide)
  rw [h3_fact, hm_fact]
