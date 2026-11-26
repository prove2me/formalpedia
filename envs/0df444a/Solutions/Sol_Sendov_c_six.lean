-- Prove2me | solution 1 for Sendov.c_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:06.228779+00:00
-- url     : https://prove2.me/submissions/ccda43a5-356b-4c59-9ea8-056fad23f359

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) : c 6 α = 1 - α / 5 - α / (2 * (3 + α)) := by norm_num [c, M]
end Sendov
