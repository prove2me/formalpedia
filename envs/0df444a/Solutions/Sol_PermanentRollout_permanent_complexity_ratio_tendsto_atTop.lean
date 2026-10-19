-- Prove2me | solution 1 for PermanentRollout.permanent_complexity_ratio_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/8308ec1c-b801-4fad-af6a-9648296c743a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_complexity_ratio_tendsto_atTop_of_superquadratic
import Theorems.Thm_PermanentRollout_permanent_superquadratic

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution :
    Filter.Tendsto
      (fun n : ℕ =>
        (circuitComplexity (permanent n) : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop Filter.atTop := by
  exact complexity_ratio_tendsto_atTop_of_superquadratic
    (fun n => circuitComplexity (permanent n)) permanent_superquadratic
end PermanentRollout
