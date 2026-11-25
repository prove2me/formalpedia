-- Prove2me | solution 1 for SmallRatio.pos_rem_of_le_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:38.075351+00:00
-- url     : https://prove2.me/submissions/1e4f0c6c-2cce-4d42-a435-9a51e1fdc59b

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_two_le_rem_of_lt_steps
public import Theorems.Thm_SmallRatio_rem_steps

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj : j ≤ steps k h) : 0 < rem k h j := by
  rcases Nat.lt_or_eq_of_le hj with hlt | heq
  · have := two_le_rem_of_lt_steps hlt; omega
  · rw [heq, rem_steps hh hhk hc]; omega
end SmallRatio
