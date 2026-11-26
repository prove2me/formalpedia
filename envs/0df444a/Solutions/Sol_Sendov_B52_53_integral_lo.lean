-- Prove2me | solution 1 for Sendov.B52_53.integral_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:42:23.912793+00:00
-- url     : https://prove2.me/submissions/5c779a23-4def-4079-a90e-05dbc4baf113

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree52_53
import Theorems.Thm_Sendov_B52_53_pev_Nmomc
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B52_53
namespace Sendov.B52_53
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 52 α t ^ 24)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 52 * (3 + α)) ^ 24) :=
  integral_moment_packed 52 24 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)
end Sendov.B52_53
