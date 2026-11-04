-- Prove2me | solution 1 for ThreeSum.CostLedger.suffixBoxes_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:59.33967+00:00
-- url     : https://prove2.me/submissions/1c6af793-e29b-4a22-8161-c84c549ddb7f

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger

set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
namespace ThreeSum.CostLedger
theorem _root_.solution (n j : ℕ) : 0 < suffixBoxes n j :=
  Nat.choose_pos (by omega)
end ThreeSum.CostLedger
