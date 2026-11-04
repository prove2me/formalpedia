-- Prove2me | solution 1 for ThreeSum.LightSortedBands.Prepared.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:24.4352+00:00
-- url     : https://prove2.me/submissions/e6d1e392-1f3b-4e83-b82a-4f63c08a3b31

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Definitions.Def_WeightedCache3SUM_Alias_695bd1ac490da0cc
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSortedBands
namespace Prepared
theorem _root_.solution {μ μ' : ℕ → ℤ} {values endpoints g bound : ℕ}
    {original : List ℤ} (h : Prepared μ values endpoints g original)
    (hk : Kept μ μ' bound) (hv : values+original.length ≤ bound)
    (he : endpoints+2+2*original.length ≤ bound) : Prepared μ' values endpoints g original := by
  apply h.transfer
  intro a ha
  exact hk a (by rcases ha with ha | ha <;> omega)
end Prepared
end ThreeSum.LightSortedBands
