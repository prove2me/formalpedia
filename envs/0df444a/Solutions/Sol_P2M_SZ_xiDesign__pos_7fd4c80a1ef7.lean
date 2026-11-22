-- Prove2me | solution 1 for P2M_SZ_xiDesign__pos_7fd4c80a1ef7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:50:50.56997+00:00
-- url     : https://prove2.me/submissions/61b2fb4c-40fa-488e-9c31-dfa6c0d3e2e9

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_Pair_sub_pos

set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) : 0 < xiDesign' α β :=
  div_pos (lt_trans zero_lt_one h.one_lt) h.sub_pos
end SZ
