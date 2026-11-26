-- Prove2me | solution 1 for Sendov.B48_49.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:40:26.252084+00:00
-- url     : https://prove2.me/submissions/83570939-985e-4e66-a2c7-2e5c8902fdfe

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree48_49
import Theorems.Thm_Sendov_B48_49_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B48_49
namespace Sendov.B48_49
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 48 α t ^ 22)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 48 * (3 + α)) ^ 22) :=
  integral_moment_packed 48 22 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B48_49
