-- Prove2me | solution 1 for SCCThm8.tau_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:14.646652+00:00
-- url     : https://prove2.me/submissions/019305de-4c6b-4920-862d-ab0c81e877a1

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
public import Theorems.Thm_SCCThm8_two_mul_choose_lt
public import Theorems.Thm_SCCThm8_choose_three_mul_le

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) : tau k < 2 ^ (3 * k - 1) := by
  have hnat : 2 * Nat.choose (3 * k) k * Nat.choose (2 * k) k < 27 ^ k := by
    have h1 := two_mul_choose_lt k hk
    have h2 := choose_three_mul_le k
    have hpos : 0 < Nat.choose (3 * k) k := Nat.choose_pos (by omega)
    calc 2 * Nat.choose (3 * k) k * Nat.choose (2 * k) k
        = Nat.choose (3 * k) k * (2 * Nat.choose (2 * k) k) := by ring
      _ < Nat.choose (3 * k) k * 4 ^ k := Nat.mul_lt_mul_of_pos_left h1 hpos
      _ ≤ 27 ^ k := h2
  have hq : (2 : ℚ) * Nat.choose (3 * k) k * Nat.choose (2 * k) k < 27 ^ k := by
    exact_mod_cast hnat
  have h8 : (8 : ℚ) ^ k = 2 ^ (3 * k - 1) * 2 := by
    rw [← pow_succ, show 3 * k - 1 + 1 = 3 * k by omega, pow_mul]; norm_num
  unfold tau
  rw [div_lt_iff₀ (by positivity), h8]
  have hp : (0 : ℚ) < 2 ^ (3 * k - 1) := by positivity
  calc (2 : ℚ) ^ (3 * k - 1) * 2 * Nat.choose (3 * k) k * Nat.choose (2 * k) k
      = 2 ^ (3 * k - 1) * (2 * Nat.choose (3 * k) k * Nat.choose (2 * k) k) := by ring
    _ < 2 ^ (3 * k - 1) * 27 ^ k := mul_lt_mul_of_pos_left hq hp
end SCCThm8
