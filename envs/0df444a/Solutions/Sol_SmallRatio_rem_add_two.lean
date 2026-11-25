-- Prove2me | solution 1 for SmallRatio.rem_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:17:52.321796+00:00
-- url     : https://prove2.me/submissions/eb279bbd-8d4f-4aee-b5fc-ec6ec9ae4739

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
namespace SmallRatio
theorem _root_.solution (j : ℕ) : rem k h (j + 2) = rem k h j % rem k h (j + 1) := rfl
end SmallRatio
