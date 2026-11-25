-- Prove2me | solution 1 for SmallRatio.rem_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:23.826418+00:00
-- url     : https://prove2.me/submissions/5934e07f-388e-49d6-969a-fc666db880fe

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_gcd_rem
public import Theorems.Thm_SmallRatio_steps_spec
public import Theorems.Thm_SmallRatio_two_le_rem_of_lt_steps
public import Theorems.Thm_SmallRatio_one_le_steps

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution : rem k h (steps k h) = 1 := by
  have hs := steps_spec hhk
  have h1 := one_le_steps hh hhk
  obtain ⟨m, hm⟩ : ∃ m, steps k h = m + 1 := ⟨steps k h - 1, by omega⟩
  have hg := gcd_rem (k := k) (h := h) m
  rw [hc, ← hm] at hg
  have h2 := two_le_rem_of_lt_steps (show m < steps k h by omega)
  rcases (show rem k h (steps k h) = 0 ∨ rem k h (steps k h) = 1 by omega) with h0 | h0
  · rw [h0, Nat.gcd_zero_right] at hg; omega
  · exact h0
end SmallRatio
