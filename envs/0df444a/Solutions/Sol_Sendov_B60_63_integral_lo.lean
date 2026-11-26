-- Prove2me | solution 1 for Sendov.B60_63.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:48:39.248987+00:00
-- url     : https://prove2.me/submissions/0f9d09ef-b862-4b6f-95c9-414f027d403e

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63
import Theorems.Thm_Sendov_B60_63_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63
namespace Sendov.B60_63
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 60 α t ^ 28)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 60 * (3 + α)) ^ 28) :=
  integral_moment_packed 60 28 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B60_63
