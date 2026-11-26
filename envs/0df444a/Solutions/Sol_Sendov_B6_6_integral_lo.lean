-- Prove2me | solution 1 for Sendov.B6_6.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:21:13.052829+00:00
-- url     : https://prove2.me/submissions/6202f38d-74a7-4206-8559-94310d657ae4

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
import Theorems.Thm_Sendov_B6_6_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6
namespace Sendov.B6_6
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 6 α t ^ 1)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 6 * (3 + α)) ^ 1) :=
  integral_moment_packed 6 1 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B6_6
