-- Prove2me | solution 1 for Sendov.B58_60.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:47:40.677183+00:00
-- url     : https://prove2.me/submissions/297737fc-020c-4c14-b34e-a0fc52347838

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60
import Theorems.Thm_Sendov_B58_60_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60
namespace Sendov.B58_60
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 58 α t ^ 27)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 58 * (3 + α)) ^ 27) :=
  integral_moment_packed 58 27 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B58_60
