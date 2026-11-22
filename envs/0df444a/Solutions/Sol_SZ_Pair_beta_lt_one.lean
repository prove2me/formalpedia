-- Prove2me | solution 1 for SZ.Pair.beta_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:47:39.201815+00:00
-- url     : https://prove2.me/submissions/008e5cdb-eef2-449c-96ad-d3faea0c3114

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_SZ_PellDesign

set_option autoImplicit false
open SZ
open SZ.Pair
variable {α β : ℝ} {a b : ℤ}
namespace SZ.Pair
theorem _root_.solution (h : Pair α β a b) : β < 1 := (abs_lt.mp h.absLt).2
end SZ.Pair
