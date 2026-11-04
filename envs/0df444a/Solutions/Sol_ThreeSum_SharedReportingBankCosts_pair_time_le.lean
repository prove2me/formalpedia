-- Prove2me | solution 1 for ThreeSum.SharedReportingBankCosts.pair_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:50:41.518008+00:00
-- url     : https://prove2.me/submissions/d549e042-665b-4bd0-a72c-b3b9adfb1008

import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_levels_eq
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_round_time_le
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_all_prefix_pos
import Theorems.Thm_ThreeSum_SharedReportingCosts_terminal_le_blocks


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankCosts
open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace ThreeSum.SharedReportingBankCosts
theorem _root_.solution (n : ℕ) :
    LightSharedReportingPair.time (half n) (blocks n) (SharedReportingBankHeader.levels (blocks n))+1000 ≤
      (roundOverhead n+1600)*allPrefixBoxes n := by
  have hsum : (∑ k ∈ Finset.range (Switch.terminalDepth n+1),
      (LightSharedReportingLevels.roundTime (half n) (blocks n) k+8)) ≤
      roundOverhead n*allPrefixBoxes n := by
    unfold allPrefixBoxes
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k hk => round_time_le
      ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans (terminal_le_blocks n)))
  have hconstant := Nat.le_mul_of_pos_right 1600 (all_prefix_pos n)
  unfold LightSharedReportingPair.time LightSharedReportingLevels.time
  rw [levels_eq,Nat.add_mul]
  omega
end ThreeSum.SharedReportingBankCosts
