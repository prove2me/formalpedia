-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.At.keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:38:42.244091+00:00
-- url     : https://prove2.me/submissions/774fab68-78e5-4152-aed5-8cf0721022ef

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandEnumeration
namespace At
theorem _root_.solution {μ μ' : ℕ → ℤ} {lo hi bound : ℕ} {A : Family}
    (h : At μ lo hi A) (hk : Kept μ μ' bound)
    (hlo : lo+A.size ≤ bound) (hhi : hi+A.size ≤ bound) : At μ' lo hi A := by
  constructor
  · intro i hi
    rw [hk (lo+i) (by omega)]
    exact h.1 i hi
  · intro i hi'
    rw [hk (hi+i) (by omega)]
    exact h.2 i hi'
end At
end ThreeSum.LightBandEnumeration
