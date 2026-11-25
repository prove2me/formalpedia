-- Prove2me | solution 1 for SmallRatio.rem_div_rem_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:13.92155+00:00
-- url     : https://prove2.me/submissions/cd6e2eb5-4ac7-4087-8e25-fa7dcf241d28

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
public import Theorems.Thm_SmallRatio_rem_succ_lt

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj : j < steps k h) : 1 ≤ rem k h j / rem k h (j + 1) := by
  have hp := pos_rem_of_le_steps hh hhk hc (show j + 1 ≤ steps k h by omega)
  have hl := rem_succ_lt hh hhk hc hj
  exact (Nat.one_le_div_iff hp).2 hl.le
end SmallRatio
