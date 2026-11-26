-- Prove2me | solution 1 for Sendov.B8_9.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:22:06.25936+00:00
-- url     : https://prove2.me/submissions/d5bcfff6-923f-41c4-bd11-67bc8287cee6

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9
import Theorems.Thm_Sendov_B8_9_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9
namespace Sendov.B8_9
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 8 α t ^ 2)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 8 * (3 + α)) ^ 2) :=
  integral_moment_packed 8 2 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B8_9
