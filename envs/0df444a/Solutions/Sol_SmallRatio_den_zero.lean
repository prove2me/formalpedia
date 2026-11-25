-- Prove2me | solution 1 for SmallRatio.den_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:18:00.382957+00:00
-- url     : https://prove2.me/submissions/72ef7a39-0719-42b3-81c5-f2739ea16c28

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
theorem _root_.solution : den k h 0 = 0 := rfl
end SmallRatio
