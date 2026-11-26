-- Prove2me | solution 1 for Sendov.B22_24.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:28:32.301802+00:00
-- url     : https://prove2.me/submissions/dbb98ab1-e11f-4feb-8e08-0c055f190dfe

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
import Theorems.Thm_Sendov_B22_24_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
namespace Sendov.B22_24
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 22 α t ^ 9)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 22 * (3 + α)) ^ 9) :=
  integral_moment_packed 22 9 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B22_24
