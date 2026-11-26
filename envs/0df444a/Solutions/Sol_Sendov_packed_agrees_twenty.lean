-- Prove2me | solution 1 for Sendov.packed_agrees_twenty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:09:04.431896+00:00
-- url     : https://prove2.me/submissions/ceb7f7f0-e9eb-4c1e-a415-861f017a8612

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20Packed
import Theorems.Thm_Sendov_integral_twenty_packed
import Theorems.Thm_Sendov_integral_moment


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 100000
open Sendov
namespace Sendov
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    pev Nmom20 α / ((L20 : ℝ) * (2 * M 20 * (3 + α)) ^ 8) = mom 20 α 8 := by
  rw [← integral_twenty_packed α hα, integral_moment]
end Sendov
