-- Prove2me | solution 1 for SZ.xiDesign_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:50:23.565878+00:00
-- url     : https://prove2.me/submissions/52268112-6b1b-48e4-b64c-990779cdd1f6

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign
import Theorems.Thm_SZ_Pair_sub_pos

set_option autoImplicit false
open SZ
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) (hβ : β < 0) : 0 < xiDesign α β :=
  div_pos (by linarith) h.sub_pos
end SZ
