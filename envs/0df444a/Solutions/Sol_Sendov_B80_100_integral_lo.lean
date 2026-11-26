-- Prove2me | solution 1 for Sendov.B80_100.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:01:52.202439+00:00
-- url     : https://prove2.me/submissions/837348ae-5d28-4580-a691-3c18094fa5be

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
import Theorems.Thm_Sendov_B80_100_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100
namespace Sendov.B80_100
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 80 α t ^ 38)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 80 * (3 + α)) ^ 38) :=
  integral_moment_packed 80 38 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B80_100
