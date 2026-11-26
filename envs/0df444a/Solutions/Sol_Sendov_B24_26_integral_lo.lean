-- Prove2me | solution 1 for Sendov.B24_26.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:29:36.111487+00:00
-- url     : https://prove2.me/submissions/fa2fadd3-2f2d-4589-97b5-9023c2a2c75b

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
import Theorems.Thm_Sendov_B24_26_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
namespace Sendov.B24_26
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 24 α t ^ 10)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 24 * (3 + α)) ^ 10) :=
  integral_moment_packed 24 10 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B24_26
