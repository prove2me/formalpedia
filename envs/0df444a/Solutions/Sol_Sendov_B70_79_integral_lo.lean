-- Prove2me | solution 1 for Sendov.B70_79.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:58:51.23917+00:00
-- url     : https://prove2.me/submissions/824412b5-76d2-4644-bdf4-b1ec3ac915d1

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree70_79
import Theorems.Thm_Sendov_B70_79_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B70_79
namespace Sendov.B70_79
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 70 α t ^ 33)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 70 * (3 + α)) ^ 33) :=
  integral_moment_packed 70 33 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B70_79
