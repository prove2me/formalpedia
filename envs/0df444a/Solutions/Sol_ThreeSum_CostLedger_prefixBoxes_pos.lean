-- Prove2me | solution 1 for ThreeSum.CostLedger.prefixBoxes_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:29.586138+00:00
-- url     : https://prove2.me/submissions/0fb1636b-2560-452b-8c51-710a0065fe67

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
import Theorems.Thm_ThreeSum_CostLedger_prefixChoices_pos
import Theorems.Thm_ThreeSum_CostLedger_suffixBoxes_pos

set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
namespace ThreeSum.CostLedger
theorem _root_.solution (n j : ℕ) : 0 < prefixBoxes n j :=
  Nat.mul_pos (prefixChoices_pos n j) (suffixBoxes_pos n j)
end ThreeSum.CostLedger
