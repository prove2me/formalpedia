-- Prove2me | solution 1 for Sendov.B40_41.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:37:17.078221+00:00
-- url     : https://prove2.me/submissions/e0ede5e3-c769-4533-ba01-c63179401967

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
import Theorems.Thm_Sendov_B40_41_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41
namespace Sendov.B40_41
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 40 α t ^ 18)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 40 * (3 + α)) ^ 18) :=
  integral_moment_packed 40 18 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B40_41
