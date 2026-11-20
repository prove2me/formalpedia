-- Prove2me | solution 1 for Sensitivity.BoolFun.restrictTo_flipBit_nonfree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:57:58.986845+00:00
-- url     : https://prove2.me/submissions/112d89fc-0abd-4a17-aa2e-bdc914fb628d

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
import Theorems.Thm_Sensitivity_embed_flipBit_nonfree

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) (x : Fin n → Bool) (i : Fin n) (hi : i ∉ free) :
    f.restrictTo free base (flipBit x i) = f.restrictTo free base x := by
  unfold restrictTo
  rw [embed_flipBit_nonfree free base x i hi]
end BoolFun
end Sensitivity
