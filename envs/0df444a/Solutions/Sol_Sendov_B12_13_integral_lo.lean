-- Prove2me | solution 1 for Sendov.B12_13.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:24:11.158873+00:00
-- url     : https://prove2.me/submissions/07f0fb19-0194-483a-8ef1-1ac042c833b4

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
import Theorems.Thm_Sendov_B12_13_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13
namespace Sendov.B12_13
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 12 α t ^ 4)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 12 * (3 + α)) ^ 4) :=
  integral_moment_packed 12 4 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B12_13
