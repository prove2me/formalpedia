-- Prove2me | solution 1 for P2M_SZ_xiDesign_seed__77c5a5c95eea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:52:52.58941+00:00
-- url     : https://prove2.me/submissions/df011964-9a64-4c07-a035-5b1a976109c7

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_Pair_sub_pos

set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) :
    xiDesign α β + xiDesign' α β = ((1 : ℤ) : ℝ) := by
  have hd := ne_of_gt h.sub_pos
  show -β / (α - β) + α / (α - β) = ((1 : ℤ) : ℝ)
  field_simp
  ring
end SZ
