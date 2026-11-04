-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.setup_time_le_budget_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:49.439305+00:00
-- url     : https://prove2.me/submissions/ace3ac6b-8d90-4f99-8c0d-aac961f6a7ff

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Theorems.Thm_ThreeSum_BandPrimeCosts_setup_time_le
import Theorems.Thm_ThreeSum_BandPrimeCosts_unit_le_budget
import Theorems.Thm_ThreeSum_LightBandPrimeDepth_depth_eq_primeDepth


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*bandCount n^2) :
    LightBandPrimeSetup.time (maxMod n) (bandSize n) R (radix n) (primeWindow n) (n^k) ≤
      timeBudget k n := by
  have ht := setup_time_le (maxMod n) (bandSize n) R (radix n) (primeWindow n) (n^k)
  rw [LightBandPrimeDepth.depth_eq_primeDepth] at ht
  refine ht.trans ?_
  unfold timeBudget
  apply Nat.add_le_add_left
  calc
    _ ≤ 5*(primeDepth radix n+1)*(3*bandCount n^2+1)*
        (LightPrimePool.size (primeWindow n)+1)^2*(3*perTripleBudget k n) := by
      gcongr
      exact unit_le_budget k hn
    _ = _ := by ring
end ThreeSum.BandPrimeCosts
