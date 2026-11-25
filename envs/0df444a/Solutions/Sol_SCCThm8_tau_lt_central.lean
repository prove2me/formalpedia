-- Prove2me | solution 1 for SCCThm8.tau_lt_central
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:43.622348+00:00
-- url     : https://prove2.me/submissions/505723e7-b4b6-45d5-8e8a-03ca11f3cd8d

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
public import Theorems.Thm_SCCThm8_central_nat

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) : tau k < Nat.choose (3 * k) (3 * k / 2) := by
  have h := central_nat k hk
  unfold trin cen at h
  have hq : (8 : ℚ) ^ k * (Nat.choose (3 * k) k * Nat.choose (2 * k) k)
      < 27 ^ k * Nat.choose (3 * k) (3 * k / 2) := by exact_mod_cast h
  unfold tau
  rw [div_lt_iff₀ (by positivity)]
  linarith
end SCCThm8
