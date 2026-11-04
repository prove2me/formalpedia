-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.actual_endpoint_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:58.108335+00:00
-- url     : https://prove2.me/submissions/1769b0a8-7362-41bf-a1de-695b91a833b8

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Theorems.Thm_ThreeSum_TernaryEntropyRates_fixedAlpha_total
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_vertices_card_eq_choose


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.TernaryEntropyRates
theorem _root_.solution (m : ℕ) :
    endpointSize m=typeCount 100000000 8908493 978268 m := by
  unfold endpointSize
  rw [TernaryTypeCardinality.vertices_card_eq_choose (fixedAlpha m) (fixedAlpha_total m)]
  change (100000000*m).choose (978268*m)*(100000000*m-978268*m).choose (8908493*m)=
    (100000000*m).choose (978268*m)*((100000000-978268)*m).choose (8908493*m)
  rw [← Nat.sub_mul]
end ThreeSum.TernaryEntropyRates
