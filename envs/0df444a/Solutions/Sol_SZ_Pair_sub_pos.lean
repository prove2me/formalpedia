-- Prove2me | solution 1 for SZ.Pair.sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:48:55.806264+00:00
-- url     : https://prove2.me/submissions/00e6d7b2-5769-4b5a-badd-2387db8ed6ad

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_Pair_beta_lt_one

set_option autoImplicit false
open SZ
open SZ.Pair
variable {α β : ℝ} {a b : ℤ}
namespace SZ.Pair
theorem _root_.solution (h : Pair α β a b) : 0 < α - β := by
  have := h.one_lt; have := h.beta_lt_one; linarith
end SZ.Pair
