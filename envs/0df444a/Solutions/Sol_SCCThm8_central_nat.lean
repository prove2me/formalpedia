-- Prove2me | solution 1 for SCCThm8.central_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:42.030613+00:00
-- url     : https://prove2.me/submissions/ef0edb97-5d78-4abf-8e66-ad8c4f9ebeac

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
public import Theorems.Thm_SCCThm8_cen_pos
public import Theorems.Thm_SCCThm8_ratio_step

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) : 8 ^ k * trin k < 27 ^ k * cen k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hs := ratio_step k
    have hc := cen_pos k
    apply Nat.lt_of_mul_lt_mul_right (a := cen k)
    calc 8 ^ (k + 1) * trin (k + 1) * cen k = 8 ^ k * (8 * trin (k + 1) * cen k) := by ring
      _ ≤ 8 ^ k * (27 * cen (k + 1) * trin k) := Nat.mul_le_mul_left _ hs
      _ = 27 * cen (k + 1) * (8 ^ k * trin k) := by ring
      _ < 27 * cen (k + 1) * (27 ^ k * cen k) :=
          Nat.mul_lt_mul_of_pos_left ih (by have := cen_pos (k + 1); positivity)
      _ = 27 ^ (k + 1) * cen (k + 1) * cen k := by ring
end SCCThm8
