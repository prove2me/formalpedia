-- Prove2me | solution 1 for RamseyLib.two_mul_choose_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:17:10.098533+00:00
-- url     : https://prove2.me/submissions/a64391df-cf76-4023-ba7d-7398dab7c1bd

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Theorems.Thm_RamseyLib_two_mul_choose_add
public import Theorems.Thm_RamseyLib_four_mul_two_pow_lt_factorial_sq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib
namespace RamseyLib
theorem _root_.solution (k n : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ (k.choose 2) := by
  have h1 : n.choose k * k.factorial ≤ n ^ k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have h2 := four_mul_two_pow_lt_factorial_sq k hk
  have h3 := two_mul_choose_add k
  have key : (2 * n.choose k * k.factorial) ^ 2 < (2 ^ (k.choose 2) * k.factorial) ^ 2 := by
    calc (2 * n.choose k * k.factorial) ^ 2 = 4 * (n.choose k * k.factorial) ^ 2 := by ring
      _ ≤ 4 * (n ^ k) ^ 2 := by gcongr
      _ = 4 * (n ^ 2) ^ k := by ring
      _ ≤ 4 * (2 ^ k) ^ k := by gcongr
      _ = 4 * 2 ^ k * 2 ^ (2 * k.choose 2) := by
        rw [← pow_mul, mul_assoc, ← pow_add]; congr 2; nlinarith
      _ < (k.factorial) ^ 2 * 2 ^ (2 * k.choose 2) := by gcongr
      _ = (2 ^ (k.choose 2) * k.factorial) ^ 2 := by ring
  have := lt_of_pow_lt_pow_left₀ 2 (by positivity) key
  exact Nat.lt_of_mul_lt_mul_right this
end RamseyLib
