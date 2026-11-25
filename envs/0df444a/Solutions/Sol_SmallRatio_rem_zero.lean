-- Prove2me | solution 1 for SmallRatio.rem_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:17:47.875646+00:00
-- url     : https://prove2.me/submissions/74f3c50d-0502-4633-9ccd-b59b8be89332

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
theorem _root_.solution : rem k h 0 = k := rfl
end SmallRatio
