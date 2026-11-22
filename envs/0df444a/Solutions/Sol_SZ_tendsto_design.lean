-- Prove2me | solution 1 for SZ.tendsto_design
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:55.179114+00:00
-- url     : https://prove2.me/submissions/18036ce8-23a3-49cd-863d-1364d590074c

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
import Theorems.Thm_SZ_xiDesign_pos


set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution (h : Pair α β a b) (hβ : β < 0) :
    Tendsto (fun n : ℕ => xiDesign α β * α ^ n) atTop atTop :=
  Tendsto.const_mul_atTop (xiDesign_pos h hβ)
    (tendsto_pow_atTop_atTop_of_one_lt h.one_lt)
end SZ
