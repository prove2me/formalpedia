-- Prove2me | solution 1 for Sendov.B50_51.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:42:13.849464+00:00
-- url     : https://prove2.me/submissions/7208f727-5e91-4bcb-bde3-ca5d49d46612

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51
import Theorems.Thm_Sendov_B50_51_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51
namespace Sendov.B50_51
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 50 α t ^ 23)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 50 * (3 + α)) ^ 23) :=
  integral_moment_packed 50 23 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B50_51
