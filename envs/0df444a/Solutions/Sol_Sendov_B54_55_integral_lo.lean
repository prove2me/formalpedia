-- Prove2me | solution 1 for Sendov.B54_55.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:44:14.17468+00:00
-- url     : https://prove2.me/submissions/22dd99a6-a77e-458e-8cd9-b822004deba2

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree54_55
import Theorems.Thm_Sendov_B54_55_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B54_55
namespace Sendov.B54_55
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 54 α t ^ 25)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 54 * (3 + α)) ^ 25) :=
  integral_moment_packed 54 25 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B54_55
