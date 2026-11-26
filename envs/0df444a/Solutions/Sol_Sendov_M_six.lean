-- Prove2me | solution 1 for Sendov.M_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:57.639139+00:00
-- url     : https://prove2.me/submissions/0b57e12b-446f-414d-8684-f285f042efdb

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution : M 6 = 5 := by norm_num [M]
end Sendov
