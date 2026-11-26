-- Prove2me | solution 1 for Sendov.B44_45.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:38:50.995352+00:00
-- url     : https://prove2.me/submissions/c86351e4-8e70-4c79-ae35-b1c638f25378

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree44_45
import Theorems.Thm_Sendov_B44_45_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B44_45
namespace Sendov.B44_45
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 44 α t ^ 20)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 44 * (3 + α)) ^ 20) :=
  integral_moment_packed 44 20 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B44_45
