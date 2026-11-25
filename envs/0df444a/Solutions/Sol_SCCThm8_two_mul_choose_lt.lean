-- Prove2me | solution 1 for SCCThm8.two_mul_choose_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:10.614852+00:00
-- url     : https://prove2.me/submissions/f2da7fd2-5844-4886-9dfe-48173301613e

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
public import Theorems.Thm_SCCThm8_centralBinom_succ_lt
public import Theorems.Thm_SCCThm8_two_mul_centralBinom_le

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) : 2 * Nat.choose (2 * k) k < 4 ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1 := centralBinom_succ_lt n
  have h2 := two_mul_centralBinom_le n (by omega)
  rw [← Nat.centralBinom_eq_two_mul_choose, pow_succ]
  omega
end SCCThm8
