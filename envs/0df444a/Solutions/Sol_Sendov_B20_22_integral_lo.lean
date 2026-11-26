-- Prove2me | solution 1 for Sendov.B20_22.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:39.694933+00:00
-- url     : https://prove2.me/submissions/7edcb069-2a21-470c-a550-a6551572354c

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22
import Theorems.Thm_Sendov_B20_22_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22
namespace Sendov.B20_22
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 20 α t ^ 8)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 20 * (3 + α)) ^ 8) :=
  integral_moment_packed 20 8 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B20_22
