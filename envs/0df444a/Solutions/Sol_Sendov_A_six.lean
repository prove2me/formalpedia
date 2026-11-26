-- Prove2me | solution 1 for Sendov.A_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:45.354795+00:00
-- url     : https://prove2.me/submissions/7e0c4594-c27d-4317-9473-bc3618bfd1ba

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) : A 6 α = 1 - 2 * α / 5 := by norm_num [A, M]
end Sendov
