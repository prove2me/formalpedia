-- Prove2me | solution 1 for P2M_SZ_xiDesign_seed__46b539b85d21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:51:18.660799+00:00
-- url     : https://prove2.me/submissions/7387f5a0-e9ce-4432-8d29-961d3544d464

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_Pair_sub_pos

set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) :
    xiDesign α β * α + xiDesign' α β * β = ((0 : ℤ) : ℝ) := by
  have hd := ne_of_gt h.sub_pos
  show -β / (α - β) * α + α / (α - β) * β = ((0 : ℤ) : ℝ)
  field_simp
  ring
end SZ
