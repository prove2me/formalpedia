-- Prove2me | solution 1 for TunnellMap.ceil_intCast_div_intCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:12.347803+00:00
-- url     : https://prove2.me/submissions/68042903-2f86-496b-b6eb-d258ac7edb75

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_floor_intCast_div_intCast

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (a b : ℤ) (hb : 0 ≤ b) :
    ⌈((a : ℚ) / (b : ℚ))⌉ = -((-a) / b) := by
  have h : ((a : ℚ) / (b : ℚ)) = -(((-a : ℤ) : ℚ) / (b : ℚ)) := by push_cast; ring
  rw [h, Int.ceil_neg, floor_intCast_div_intCast _ _ hb]
end TunnellMap
