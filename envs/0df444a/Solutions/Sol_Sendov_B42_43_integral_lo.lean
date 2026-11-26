-- Prove2me | solution 1 for Sendov.B42_43.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:38:02.794854+00:00
-- url     : https://prove2.me/submissions/c687c29e-dbb1-46bd-b671-ec327d3b3331

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree42_43
import Theorems.Thm_Sendov_B42_43_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B42_43
namespace Sendov.B42_43
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 42 α t ^ 19)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 42 * (3 + α)) ^ 19) :=
  integral_moment_packed 42 19 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B42_43
