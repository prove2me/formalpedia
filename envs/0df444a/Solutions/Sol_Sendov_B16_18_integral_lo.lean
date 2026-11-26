-- Prove2me | solution 1 for Sendov.B16_18.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:25:55.550857+00:00
-- url     : https://prove2.me/submissions/407b9b41-ef6e-48e6-910b-810c432fc6fa

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
import Theorems.Thm_Sendov_B16_18_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18
namespace Sendov.B16_18
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 16 α t ^ 6)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 16 * (3 + α)) ^ 6) :=
  integral_moment_packed 16 6 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B16_18
