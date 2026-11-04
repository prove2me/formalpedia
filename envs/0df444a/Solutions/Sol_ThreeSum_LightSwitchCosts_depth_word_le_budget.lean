-- Prove2me | solution 1 for ThreeSum.LightSwitchCosts.depth_word_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:31:03.115206+00:00
-- url     : https://prove2.me/submissions/06cfa26c-b508-47ad-865c-52e9b674b80c

import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Theorems.Thm_ThreeSum_LightScales_blockCount_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchCosts
open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology
namespace ThreeSum.LightSwitchCosts
theorem _root_.solution (n : ℕ) :
    LightSwitchDepth.word (blockCount (inputBits n)) ≤ wordBudget n := by
  have hJ := LightScales.blockCount_le (inputBits n)
  have hbase : 300*inputBits n+1001 ≤ wordBudget n :=
    Nat.le_self_pow (by decide : (64 : ℕ) ≠ 0) _
  unfold LightSwitchDepth.word
  omega
end ThreeSum.LightSwitchCosts
