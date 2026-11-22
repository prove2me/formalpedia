-- Prove2me | solution 1 for SZ.Pair.neg_one_lt_beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:52:35.426681+00:00
-- url     : https://prove2.me/submissions/f551b80e-c41f-48f1-bc12-07009a930d9d

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign

set_option autoImplicit false
open SZ
open SZ.Pair
variable {α β : ℝ} {a b : ℤ}
namespace SZ.Pair
theorem _root_.solution (h : Pair α β a b) : -1 < β := (abs_lt.mp h.absLt).1
end SZ.Pair
