-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBuild.endpointLeft_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:53.764281+00:00
-- url     : https://prove2.me/submissions/628802cf-2ddc-42b9-b708-b6345ed4ea8a

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_flat_bound
import Theorems.Thm_ThreeSum_BlockCoefficientRows_eval_left
import Definitions.Def_WeightedCache3SUM_Alias_2f39c5fb289e3702


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000
namespace ThreeSum.LightBlockSourceBuild
theorem _root_.solution {h J : ℕ} (o : Occurrences h J)
    (S : Finset (BlockRows.Coord J (512*h))) :
    |endpointLeft o S| ≤ (endpointBound h J : ℤ) := by
  rw [← eval_left o S,Int.abs_natCast]
  exact Int.ofNat_le.mpr (OneHotMask.eval_le
    (fun _ hi => flat_bound o false hi) (fun _ hi => flat_bound o true hi))
end ThreeSum.LightBlockSourceBuild
