-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBuild.endpointRight_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:20.382909+00:00
-- url     : https://prove2.me/submissions/ef2d94ad-d807-45db-813c-68f90b80642a

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_flat_bound
import Theorems.Thm_ThreeSum_BlockCoefficientRows_eval_right
import Definitions.Def_WeightedCache3SUM_Alias_2f39c5fb289e3702


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000
namespace ThreeSum.LightBlockSourceBuild
theorem _root_.solution {h J : ℕ} (o : Occurrences h J)
    (S : Finset (BlockRows.Coord J (512*h))) :
    |endpointRight o S| ≤ (endpointBound h J : ℤ) := by
  rw [← eval_right o S,Int.abs_natCast]
  exact Int.ofNat_le.mpr (OneHotMask.eval_le
    (fun _ hi => flat_bound o true hi) (fun _ hi => flat_bound o false hi))
end ThreeSum.LightBlockSourceBuild
