-- Prove2me | solution 1 for Sendov.B26_27.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:31:48.122149+00:00
-- url     : https://prove2.me/submissions/dbc38aff-ad01-4698-8f49-8a24235f6edd

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27
import Theorems.Thm_Sendov_B26_27_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27
namespace Sendov.B26_27
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 26 α t ^ 11)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 26 * (3 + α)) ^ 11) :=
  integral_moment_packed 26 11 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B26_27
