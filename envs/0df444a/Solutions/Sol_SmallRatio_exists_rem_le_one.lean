-- Prove2me | solution 1 for SmallRatio.exists_rem_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:24:28.668787+00:00
-- url     : https://prove2.me/submissions/aa4b0499-50f5-4c48-ac97-b5f44cc0a2f3

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_le_of_ge_two

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
namespace SmallRatio
theorem _root_.solution : ∃ j ≤ h + 1, rem k h j ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have := rem_le_of_ge_two (k := k) (h := h) h (fun i hi => hcon i hi)
  have := hcon (h + 1) le_rfl
  omega
end SmallRatio
