-- Prove2me | solution 1 for ThreeSum.LightSparseQuery.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:15.495978+00:00
-- url     : https://prove2.me/submissions/eca14175-ec58-437d-9400-99369b7ccac1

import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
import Definitions.Def_Submission_ThreeSum_LightSparseQuery
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightExplicitSum_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
import Theorems.Thm_ThreeSum_LightMaskMinimum_time_bound
import Theorems.Thm_ThreeSum_LightQueryBox_time_bound
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightSparseQuery
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open scoped BigOperators
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSparseQuery
theorem _root_.solution {W c t : ℕ} (hc : c ≤ W) (ht : t ≤ c+1) :
    time W c t ≤ 14000*(W+1)^3*(queryItems c t+1) := by
  have he := LightExplicitSum.time_bound (c := c) (by omega : t ≤ W+1)
  have hb := LightCanonicalBoxSum.time_bound (t := t) hc
  have ho : layerOffset c t+1 ≤ queryItems c t+1 := by unfold queryItems; omega
  have hh : c.choose t+1 ≤ queryItems c t+1 := by unfold queryItems; omega
  have hp : (W+1)^2 ≤ (W+1)^3 := by nlinarith
  have he' := he.trans (Nat.mul_le_mul_left (8200*(W+1)^3) ho)
  have hb' := hb.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 5200 hp) hh)
  have hpos : 1 ≤ queryItems c t+1 := by omega
  unfold time LightSign.time
  nlinarith
end ThreeSum.LightSparseQuery
