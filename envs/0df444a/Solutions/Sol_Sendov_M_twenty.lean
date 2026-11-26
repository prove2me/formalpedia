-- Prove2me | solution 1 for Sendov.M_twenty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:44.019529+00:00
-- url     : https://prove2.me/submissions/16ee5c10-6616-40b8-9569-52a10efc7d9a

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20

set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution : M 20 = 19 := by norm_num [M]
end Sendov
