-- Prove2me | solution 1 for SmallRatio.rem_le_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:06.3409+00:00
-- url     : https://prove2.me/submissions/ae769fe4-d2b4-4d2c-a513-21cba0cc5faa

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_strictAnti

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps k h) : rem k h j ≤ h := by
  rcases Nat.lt_or_eq_of_le hj1 with h1 | h1
  · exact (rem_strictAnti hh hhk hc h1 hj).le
  · subst h1; rfl
end SmallRatio
