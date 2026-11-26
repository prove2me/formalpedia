-- Prove2me | solution 1 for Sendov.lowJ_four_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:26.756821+00:00
-- url     : https://prove2.me/submissions/1a2b2d01-0f75-4f2d-8220-ac32c442666c

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_lowJ_four

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℝ) :
    1 - lowJ 4 a = ((1 - a) ^ 3 * (1 + a) / 5) * (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by
  rw [lowJ_four]
  ring
end Sendov
