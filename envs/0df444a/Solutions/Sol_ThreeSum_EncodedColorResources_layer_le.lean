-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.layer_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:04:45.476451+00:00
-- url     : https://prove2.me/submissions/48fae470-cc5e-450b-ae29-02a2193ea242

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_local_bounds

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : outputCount (512*half n) (half n) ≤ scale n := by
  have hh : outputCount (512*half n) (half n) ≤ 2^(512*half n) := Nat.choose_le_two_pow _ _
  have hp : 2^(512*half n) ≤ scale n := by have h := (local_bounds n).maskPower; have hh := Nat.two_pow_pos (512*half n); rw [pow_succ] at h; omega
  exact hh.trans hp
end ThreeSum.EncodedColorResources
