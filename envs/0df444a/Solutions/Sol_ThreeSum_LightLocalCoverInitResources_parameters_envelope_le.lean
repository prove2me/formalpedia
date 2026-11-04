-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.parameters_envelope_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:33:14.80101+00:00
-- url     : https://prove2.me/submissions/86b25f36-3046-4f15-9288-3e2a25a3c439

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution (h : ℕ) :
    LocalParameterBounds.envelope h ≤ LightLocalCoverResources.envelope h := by
  unfold LocalParameterBounds.envelope LightLocalCoverResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (h*h)]
end ThreeSum.LightLocalCoverInitResources
