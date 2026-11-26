-- Prove2me | solution 1 for TunnellMap.floor_intCast_div_intCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:02.192701+00:00
-- url     : https://prove2.me/submissions/84f911e7-7988-45ff-8ef4-5d3b5a2be295

import Mathlib
import Definitions.Def_TunnellMap_KernelArith

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (a b : ℤ) (hb : 0 ≤ b) :
    ⌊((a : ℚ) / (b : ℚ))⌋ = a / b := by
  rw [Int.floor_div_cast_of_nonneg hb, Int.floor_intCast]
end TunnellMap
