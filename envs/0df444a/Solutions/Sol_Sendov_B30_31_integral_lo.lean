-- Prove2me | solution 1 for Sendov.B30_31.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:31:55.237962+00:00
-- url     : https://prove2.me/submissions/b2c9c340-b2a2-416f-a1f9-1a5a90db7588

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31
import Theorems.Thm_Sendov_B30_31_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31
namespace Sendov.B30_31
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 30 α t ^ 13)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 30 * (3 + α)) ^ 13) :=
  integral_moment_packed 30 13 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B30_31
