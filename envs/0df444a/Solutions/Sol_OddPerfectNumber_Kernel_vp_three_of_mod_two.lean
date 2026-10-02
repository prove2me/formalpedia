-- Prove2me | solution 1 for OddPerfectNumber.Kernel.vp_three_of_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T19:53:27.696783+00:00
-- url     : https://prove2.me/submissions/86ac9f00-58ec-477a-b9fe-4eaf16c35e2f

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

theorem solution (n : Nat) (hn : n % 3 = 2) :
    (n ^ 2 - n + 1).factorization 3 = 1 := by
  have hn_eq : n = 3 * (n / 3) + 2 := by omega
  set k := n / 3
  have h_le : n ≤ n ^ 2 := by
    have : 1 ≤ n := by omega
    nlinarith
  have h_sub : (n ^ 2 - n + 1) + n = n ^ 2 + 1 := by omega
  have h_sum : 3 * (3 * (k ^ 2 + k) + 1) + n = n ^ 2 + 1 := by
    rw [hn_eq]
    ring
  have hN : n ^ 2 - n + 1 = 3 * (3 * (k ^ 2 + k) + 1) := by omega
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
