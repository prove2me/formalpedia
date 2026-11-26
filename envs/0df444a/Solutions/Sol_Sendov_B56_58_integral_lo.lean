-- Prove2me | solution 1 for Sendov.B56_58.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:45:35.81089+00:00
-- url     : https://prove2.me/submissions/52fbd16f-2059-4643-8343-148195361eb9

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree56_58
import Theorems.Thm_Sendov_B56_58_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B56_58
namespace Sendov.B56_58
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 56 α t ^ 26)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 56 * (3 + α)) ^ 26) :=
  integral_moment_packed 56 26 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B56_58
