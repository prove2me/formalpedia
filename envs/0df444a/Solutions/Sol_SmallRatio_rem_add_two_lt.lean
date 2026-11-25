-- Prove2me | solution 1 for SmallRatio.rem_add_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:21:52.186801+00:00
-- url     : https://prove2.me/submissions/905d0ee6-a68e-4be9-9c9a-1dc18c5da721

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_add_two

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
namespace SmallRatio
theorem _root_.solution (j : ℕ) (hpos : 0 < rem k h (j + 1)) : rem k h (j + 2) < rem k h (j + 1) := by
  rw [rem_add_two]; exact Nat.mod_lt _ hpos
end SmallRatio
