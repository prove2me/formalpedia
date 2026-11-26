-- Prove2me | solution 1 for Sendov.B14_15.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:24:59.114816+00:00
-- url     : https://prove2.me/submissions/68df8168-2f92-475d-b60d-73a176023638

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
import Theorems.Thm_Sendov_B14_15_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15
namespace Sendov.B14_15
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 14 α t ^ 5)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 14 * (3 + α)) ^ 5) :=
  integral_moment_packed 14 5 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B14_15
