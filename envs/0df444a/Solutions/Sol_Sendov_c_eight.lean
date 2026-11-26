-- Prove2me | solution 1 for Sendov.c_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:17:07.840906+00:00
-- url     : https://prove2.me/submissions/58bc51c7-d38c-45e9-b309-5007144ec65b

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree8

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (α : ℝ) : c 8 α = 1 - α / 7 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring
end Sendov
