-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.primeDepth_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:50.178459+00:00
-- url     : https://prove2.me/submissions/bd75b879-0b6c-4567-9402-6b50c7710583

import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
import Definitions.Def_WeightedCache3SUM_Alias_5892d665e4005f14
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Filter Real Scales BandScales CostLedger Parameters StageBounds HierarchyScales
  ArithmeticStageBounds
open scoped Topology
set_option maxHeartbeats 1400000
noncomputable section
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution : PowerBound (primeDepth radix) 0 := by
  apply PowerBound.of_rate
  apply squeeze_zero' _ _ primeDepth_log_ratio_tendsto_zero
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Real.log_natCast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg _))
      (Real.log_nonneg (by exact_mod_cast hn))
end ThreeSum.BandPrimeCosts
