-- Prove2me | solution 1 for Sensitivity.BoolFun.restrictTo_not_sensitiveAt_nonfree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:58:33.454003+00:00
-- url     : https://prove2.me/submissions/ff4e8fbc-183e-4a8f-abbe-12950345e56b

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
import Theorems.Thm_Sensitivity_BoolFun_restrictTo_flipBit_nonfree

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) (x : Fin n → Bool) (i : Fin n) (hi : i ∉ free) :
    ¬(f.restrictTo free base).sensitiveAt x i := by
  unfold sensitiveAt
  push_neg
  exact f.restrictTo_flipBit_nonfree free base x i hi
end BoolFun
end Sensitivity
