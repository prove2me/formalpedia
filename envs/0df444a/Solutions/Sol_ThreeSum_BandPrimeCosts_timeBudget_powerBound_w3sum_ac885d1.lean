-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.timeBudget_powerBound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:19.853697+00:00
-- url     : https://prove2.me/submissions/2659424f-ccea-4647-b574-6a12a09423b4

import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
import Theorems.Thm_ThreeSum_BandPrimeCosts_primeDepth_powerBound
import Theorems.Thm_ThreeSum_BandPrimeCosts_pool_time_powerBound
import Theorems.Thm_ThreeSum_BandPrimeCosts_prime_size_powerBound
import Theorems.Thm_ThreeSum_BandPrimeCosts_owner_count_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_d4d3bf606820e931
import Theorems.Thm_ThreeSum_Parameters_E_bounds
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_pow


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Filter Real Scales BandScales CostLedger Parameters StageBounds HierarchyScales
  ArithmeticStageBounds
open scoped Topology
set_option maxHeartbeats 1400000
noncomputable section
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution (k : ℕ) :
    PowerBound (timeBudget k) (2+epsilon*(4/5-(2/5)*E-2*bandShift)) := by
  have hdepth := primeDepth_powerBound.add_same (PowerBound.const 1)
  have hsize := (prime_size_powerBound.add_same (PowerBound.const 1)).pow 2
  have hh := ((((PowerBound.const 15).mul hdepth).mul owner_count_powerBound).mul hsize).mul
    (perTriple_powerBound k)
  have heq : (0 : ℝ)+2*(1-(E+bandShift)/5)+0+(8/5)*((E+1/2)/5)=
      2+epsilon*(4/5-(2/5)*E-2*bandShift) := by unfold epsilon; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [heq] at hh
  have he : (0 : ℝ) ≤ 2+epsilon*(4/5-(2/5)*E-2*bandShift) := by
    have hh := E_bounds.2
    unfold epsilon bandShift
    linarith
  exact (pool_time_powerBound.mono_exponent he).add_same hh
end ThreeSum.BandPrimeCosts
