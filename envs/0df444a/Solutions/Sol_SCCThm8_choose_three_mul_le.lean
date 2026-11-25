-- Prove2me | solution 1 for SCCThm8.choose_three_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:14.962796+00:00
-- url     : https://prove2.me/submissions/5b6c2c08-2598-4384-b7ab-ec11814507f1

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) : Nat.choose (3 * k) k * 4 ^ k ≤ 27 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hterm : k ^ k * (2 * k) ^ (3 * k - k) * Nat.choose (3 * k) k ≤ (k + 2 * k) ^ (3 * k) := by
    rw [add_pow]
    exact Finset.single_le_sum (f := fun m => k ^ m * (2 * k) ^ (3 * k - m) * (3 * k).choose m)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  have e1 : k ^ k * (2 * k) ^ (3 * k - k) * Nat.choose (3 * k) k =
      k ^ (3 * k) * (Nat.choose (3 * k) k * 4 ^ k) := by
    rw [show 3 * k - k = 2 * k by omega, mul_pow, pow_mul, show 3 * k = k + 2 * k by ring,
      pow_add]
    norm_num; ring
  have e2 : (k + 2 * k) ^ (3 * k) = k ^ (3 * k) * 27 ^ k := by
    rw [show k + 2 * k = 3 * k by ring, mul_pow, pow_mul]; norm_num; ring
  rw [e1, e2] at hterm
  exact Nat.le_of_mul_le_mul_left hterm (by positivity)
end SCCThm8
