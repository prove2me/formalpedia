-- Prove2me | solution 1 for Sendov.B18_20.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:38.962795+00:00
-- url     : https://prove2.me/submissions/a579b9c5-b962-4832-8a1d-2b413643301e

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
import Theorems.Thm_Sendov_B18_20_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
namespace Sendov.B18_20
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 18 α t ^ 7)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 18 * (3 + α)) ^ 7) :=
  integral_moment_packed 18 7 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B18_20
