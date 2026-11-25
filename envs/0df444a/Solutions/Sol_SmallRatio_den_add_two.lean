-- Prove2me | solution 1 for SmallRatio.den_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:18:05.360513+00:00
-- url     : https://prove2.me/submissions/faf841ec-6043-4399-9f04-1707861655f4

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
theorem _root_.solution (j : ℕ) :
    den k h (j + 2) = rem k h j / rem k h (j + 1) * den k h (j + 1) + den k h j := rfl
end SmallRatio
