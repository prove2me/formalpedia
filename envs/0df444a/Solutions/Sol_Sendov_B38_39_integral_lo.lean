-- Prove2me | solution 1 for Sendov.B38_39.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:36:12.101343+00:00
-- url     : https://prove2.me/submissions/0a547645-235b-4420-8855-e23dca779e40

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39
import Theorems.Thm_Sendov_B38_39_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B38_39
namespace Sendov.B38_39
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 38 α t ^ 17)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 38 * (3 + α)) ^ 17) :=
  integral_moment_packed 38 17 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B38_39
