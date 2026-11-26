-- Prove2me | solution 1 for Sendov.B34_35.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:34:36.182281+00:00
-- url     : https://prove2.me/submissions/0ec2fcec-ab95-4470-9732-6b060f3ffcd4

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35
import Theorems.Thm_Sendov_B34_35_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B34_35
namespace Sendov.B34_35
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 34 α t ^ 15)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 34 * (3 + α)) ^ 15) :=
  integral_moment_packed 34 15 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B34_35
