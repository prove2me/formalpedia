-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.actual_output_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:15:56.784923+00:00
-- url     : https://prove2.me/submissions/18ced2a8-9e11-411a-ba64-5530394aeaf0

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_total
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
    outputSize m=typeCount 100000000 15860450 2934804 m := by
  unfold outputSize
  rw [TernaryTypeCardinality.vertices_card_eq_choose (fixedPi m) (fixedPi_total m)]
  change (100000000*m).choose (2934804*m)*(100000000*m-2934804*m).choose (15860450*m)=
    (100000000*m).choose (2934804*m)*((100000000-2934804)*m).choose (15860450*m)
  rw [← Nat.sub_mul]
end ThreeSum.TernaryEntropyRates
