-- Prove2me | solution 1 for Sendov.B32_33.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:33:49.015841+00:00
-- url     : https://prove2.me/submissions/22835b74-2c5e-44b0-86be-6a9ef5b56fcc

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
import Theorems.Thm_Sendov_B32_33_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33
namespace Sendov.B32_33
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 32 α t ^ 14)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 32 * (3 + α)) ^ 14) :=
  integral_moment_packed 32 14 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B32_33
