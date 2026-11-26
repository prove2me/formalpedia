-- Prove2me | solution 1 for Sendov.M_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:01.416329+00:00
-- url     : https://prove2.me/submissions/9434fca1-a7e0-4b51-b67d-c96b4ec95c1f

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution : M 5 = 4 := by norm_num [M]
end Sendov
