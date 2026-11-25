-- Prove2me | solution 1 for SmallRatio.rem_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:17:49.04223+00:00
-- url     : https://prove2.me/submissions/d2d7571f-727c-46f1-bf46-19f04140472a

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
theorem _root_.solution : rem k h 1 = h := rfl
end SmallRatio
