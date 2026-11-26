-- Prove2me | solution 1 for Sendov.B36_37.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:35:29.906942+00:00
-- url     : https://prove2.me/submissions/ed0628c9-5f96-4426-b47a-a94ebb57ce47

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
import Theorems.Thm_Sendov_B36_37_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37
namespace Sendov.B36_37
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 36 α t ^ 16)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 36 * (3 + α)) ^ 16) :=
  integral_moment_packed 36 16 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B36_37
