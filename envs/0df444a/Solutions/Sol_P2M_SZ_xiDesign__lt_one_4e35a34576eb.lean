-- Prove2me | solution 1 for P2M_SZ_xiDesign__lt_one_4e35a34576eb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:50:51.075037+00:00
-- url     : https://prove2.me/submissions/27b4f162-28f9-48f4-a578-809dd4e8d948

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_Pair_sub_pos

set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) (hβ : β < 0) : xiDesign' α β < 1 := by
  have hd := h.sub_pos
  show α / (α - β) < 1
  rw [div_lt_one hd]; linarith
end SZ
