-- Prove2me | solution 1 for Sendov.B46_47.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:42.917574+00:00
-- url     : https://prove2.me/submissions/f890f6d3-3eb7-473d-aeb9-cc00d3770a47

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
import Theorems.Thm_Sendov_B46_47_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47
namespace Sendov.B46_47
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 46 α t ^ 21)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 46 * (3 + α)) ^ 21) :=
  integral_moment_packed 46 21 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B46_47
