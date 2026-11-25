-- Prove2me | solution 1 for SmallRatio.two_rem_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:31.618464+00:00
-- url     : https://prove2.me/submissions/379a7ba5-5861-4fb3-b689-4eb7cac2ee17

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_add_two
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
public import Theorems.Thm_SmallRatio_rem_succ_lt
public import Theorems.Thm_SmallRatio_rem_div_rem_pos

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj : j + 1 < steps k h) : 2 * rem k h (j + 2) < rem k h j := by
  have hp := pos_rem_of_le_steps hh hhk hc (show j + 1 ≤ steps k h by omega)
  have hl := rem_succ_lt hh hhk hc (show j < steps k h by omega)
  have hmod := Nat.mod_add_div (rem k h j) (rem k h (j + 1))
  have hlt := Nat.mod_lt (rem k h j) hp
  have ha := rem_div_rem_pos hh hhk hc (show j < steps k h by omega)
  rw [rem_add_two]
  set a := rem k h j / rem k h (j + 1)
  set b := rem k h (j + 1)
  set c := rem k h j % rem k h (j + 1)
  rcases Nat.lt_or_ge a 2 with h2 | h2
  · have : a = 1 := by omega
    rw [this] at hmod; omega
  · nlinarith
end SmallRatio
