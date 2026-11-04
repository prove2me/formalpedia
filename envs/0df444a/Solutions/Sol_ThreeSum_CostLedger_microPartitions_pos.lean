-- Prove2me | solution 1 for ThreeSum.CostLedger.microPartitions_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:58.191969+00:00
-- url     : https://prove2.me/submissions/b67923b8-77aa-4479-b099-2052a2116e22

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger

set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
namespace ThreeSum.CostLedger
theorem _root_.solution (n : ℕ) : 0 < microPartitions n :=
  Nat.choose_pos (Nat.div_le_self _ _)
end ThreeSum.CostLedger
