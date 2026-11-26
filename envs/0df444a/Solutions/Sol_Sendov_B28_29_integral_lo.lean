-- Prove2me | solution 1 for Sendov.B28_29.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:30:47.364639+00:00
-- url     : https://prove2.me/submissions/65cb8970-bfb2-4f80-9e47-df245c91af18

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
import Theorems.Thm_Sendov_B28_29_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
namespace Sendov.B28_29
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 28 α t ^ 12)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 28 * (3 + α)) ^ 12) :=
  integral_moment_packed 28 12 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B28_29
