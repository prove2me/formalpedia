-- Prove2me | solution 1 for ThreeSum.CostLedger.prefixChoices_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:50.263464+00:00
-- url     : https://prove2.me/submissions/923701ab-3cf3-4efc-bcab-6c5b8a92db4d

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
import Theorems.Thm_ThreeSum_CostLedger_microOutputs_pos
import Theorems.Thm_ThreeSum_CostLedger_microPartitions_pos

set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
namespace ThreeSum.CostLedger
theorem _root_.solution (n j : ℕ) : 0 < prefixChoices n j :=
  Nat.pow_pos (Nat.mul_pos (microOutputs_pos n) (microPartitions_pos n))
end ThreeSum.CostLedger
