-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.space_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:29.126881+00:00
-- url     : https://prove2.me/submissions/c9bf1ea3-f861-47ea-868d-b90f721cf85f

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_parameters_envelope_le
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_constant_le
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_four_envelope_le
import Theorems.Thm_ThreeSum_LightLocalCoverResources_space_bound
import Definitions.Def_WeightedCache3SUM_Alias_f0a4e431f2aa2c77


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution (free h : ℕ) : LightLocalCoverInit.space free h ≤ free+envelope h := by
  have hp := (LocalParameterBounds.space_bound (LightLocalCoverInit.base free) h).trans
    (Nat.add_le_add_left (parameters_envelope_le h) (LightLocalCoverInit.base free))
  have hc := LightLocalCoverResources.space_bound (LightLocalCoverInit.base free) h
  have hk := constant_le h
  have hm : LightLocalCoverInit.space free h ≤ free+4*LightLocalCoverResources.envelope h := by
    unfold LightLocalCoverInit.space LightLocalCoverInit.base at *
    omega
  exact hm.trans (Nat.add_le_add_left (four_envelope_le h) free)
end ThreeSum.LightLocalCoverInitResources
