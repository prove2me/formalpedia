-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBuild.flat_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:04.602793+00:00
-- url     : https://prove2.me/submissions/f8ccede2-5f2e-4fce-9d55-116148f30a0b

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Theorems.Thm_ThreeSum_BlockCoefficientRows_flat_le
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_le
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_lt
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000
namespace ThreeSum.LightBlockSourceBuild
theorem _root_.solution {h J : ℕ} (o : Occurrences h J) (b : Bool) {i : ℕ}
    (hi : i < J*(512*h)) :
    flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h b) i ≤
      localPrime h^J*localPrime h := by
  exact flat_le (localPrime_pos h) (fun _ hj => occurrenceIndices_lt o hj)
    (fun _ hs _ hk => mapRow_le b hs hk) hi
end ThreeSum.LightBlockSourceBuild
