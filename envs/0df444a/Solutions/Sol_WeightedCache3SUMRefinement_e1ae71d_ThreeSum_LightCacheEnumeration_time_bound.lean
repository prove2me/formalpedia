-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:14:03.446351+00:00
-- url     : https://prove2.me/submissions/cd69fa84-9b1b-4476-8ca1-cfad32dfa386

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_visits_le_codes
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_visits_le_codes


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
theorem _root_.solution (N T : ℕ) :
    time N T ≤ 300*((N+1)*(codes N T).length) := by
  exact Nat.mul_le_mul_left 300 (visits_le_codes N T)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
