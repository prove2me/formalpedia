-- Prove2me | solution 1 for ThreeSum.LightBandRawACatalog.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:45.225567+00:00
-- url     : https://prove2.me/submissions/ff119881-6586-4b60-8216-e9542e258b6b

import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Theorems.Thm_ThreeSum_LightBandCandidates_time_bound
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Theorems.Thm_ThreeSum_LightBandRawA_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawACatalog
open Light BandEnumeration BandCandidateRows BandRawA
set_option maxHeartbeats 2100000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {tables rec src headerA headerB headerC nA nB nC g vals : ℕ} {f : ℕ → ℤ}
namespace ThreeSum.LightBandRawACatalog
theorem _root_.solution (a b c g : ℕ) :
    time a b c g ≤ 3000*(LightBandEnumeration.count a b c+a+b+c+1)*(g+1) := by
  have hc := LightBandCandidates.time_bound a b c
  have hr := LightBandRawA.time_bound (LightBandEnumeration.count a b c) g
  unfold time
  nlinarith
end ThreeSum.LightBandRawACatalog
