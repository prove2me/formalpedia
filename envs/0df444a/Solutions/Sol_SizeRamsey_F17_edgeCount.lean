-- Prove2me | solution 1 for SizeRamsey.F17_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:10.17185+00:00
-- url     : https://prove2.me/submissions/4608c2a6-d110-435f-9948-5415bc9abae5

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution : edgeCount F17 = 17 := by
  rw [edgeCount_eq_card]
  decide
end SizeRamsey
