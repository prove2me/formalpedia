-- Prove2me | solution 1 for Sendov.B64_69.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:50:11.245692+00:00
-- url     : https://prove2.me/submissions/93e82888-9a94-4028-96b6-032d5a294a34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree64_69
import Theorems.Thm_Sendov_B64_69_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B64_69
namespace Sendov.B64_69
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 64 α t ^ 30)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 64 * (3 + α)) ^ 30) :=
  integral_moment_packed 64 30 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B64_69
