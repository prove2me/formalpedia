-- Prove2me | solution 1 for ThreeSum.ArithmeticStageBounds.invocation_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:47.36226+00:00
-- url     : https://prove2.me/submissions/398db094-f132-4a17-bb32-894baf2975c2

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_remainder_bits_le
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_f1c95625e9077016
import Theorems.Thm_ThreeSum_ModuloRuntime_time_mono


set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.ArithmeticStageBounds
theorem _root_.solution {n p nA nB nC : ℕ} (k : ℕ)
    (hn : 0 < n) (hp : p ≤ maxMod n)
    (ha : nA ≤ bandSize n) (hb : nB ≤ bandSize n) (hc : nC ≤ bandSize n) :
    LightModuloCounts.time p nA nB nC (n^k) ≤ perTripleBudget k n := by
  have ht := ModuloRuntime.time_mono hp nA nB nC (n^k)
  have hbnd := ModuloCosts.time_bound (maxMod n) nA nB nC (bandSize n) (n^k) ha hb hc
  have hm := Nat.mul_le_mul_left (bandSize n) (remainder_bits_le k hn)
  unfold perTripleBudget
  omega
end ThreeSum.ArithmeticStageBounds
