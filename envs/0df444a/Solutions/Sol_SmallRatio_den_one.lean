-- Prove2me | solution 1 for SmallRatio.den_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:17:51.216041+00:00
-- url     : https://prove2.me/submissions/b7b11a33-209a-4471-ae72-f62beb408477

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
theorem _root_.solution : den k h 1 = 1 := rfl
end SmallRatio
