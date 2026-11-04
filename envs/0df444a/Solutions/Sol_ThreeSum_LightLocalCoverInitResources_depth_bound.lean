-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:00.1923+00:00
-- url     : https://prove2.me/submissions/0cda541d-d97c-4afd-9ce5-79e9328a7f36

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_constant_le
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_four_envelope_le
import Theorems.Thm_ThreeSum_LightLocalCoverResources_depth_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution (h : ℕ) : 512*h+9 ≤ envelope h := by
  have hc := LightLocalCoverResources.depth_bound h
  have hk := constant_le h
  exact (by omega : 512*h+9 ≤ 4*LightLocalCoverResources.envelope h).trans (four_envelope_le h)
end ThreeSum.LightLocalCoverInitResources
