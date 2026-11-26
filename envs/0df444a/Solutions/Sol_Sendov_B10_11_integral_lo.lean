-- Prove2me | solution 1 for Sendov.B10_11.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:23:05.220551+00:00
-- url     : https://prove2.me/submissions/d82f0cbe-525c-4a14-8ffd-7927a975cb85

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11
import Theorems.Thm_Sendov_B10_11_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11
namespace Sendov.B10_11
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 10 α t ^ 3)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 10 * (3 + α)) ^ 3) :=
  integral_moment_packed 10 3 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B10_11
