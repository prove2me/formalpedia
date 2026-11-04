-- Prove2me | solution 1 for ThreeSum.LightBandEnumeration.Tables.covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:21:55.223926+00:00
-- url     : https://prove2.me/submissions/e9fdb61c-7a74-45ab-8282-17374aaa17b5

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Theorems.Thm_ThreeSum_LightBandEnumeration_lookup_complete
import Theorems.Thm_ThreeSum_BandEnumeration_Family_lookup_complete


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandEnumeration
namespace Tables
theorem _root_.solution {μ : ℕ → ℤ} {dst : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (i : A.Index) (j : B.Index) (k : C.Index)
    (hr : relevant A B C (i,j,k)) :
    μ (dst+j.val*C.size+k.val) = (i.val+1 : ℕ) ∨
      μ (dst+B.size*C.size+i.val*B.size+j.val) = (k.val+1 : ℕ) ∨
      μ (dst+B.size*C.size+A.size*B.size+i.val*C.size+k.val) = (j.val+1 : ℕ) := by
  change A.lower i ≤ C.upper k-B.lower j ∧ C.lower k-B.upper j ≤ A.upper i at hr
  by_cases hfirst : A.lower i < C.lower k-B.upper j
  · left
    rw [ht.1 j j.isLt k k.isLt,lookup_complete A i.isLt (by omega) hr.2]
  · by_cases hsecond : A.lower i+B.lower j ≤ C.lower k
    · right; right
      rw [ht.2.2 i i.isLt k k.isLt,lookup_complete B j.isLt (by omega) (by omega)]
    · right; left
      rw [ht.2.1 i i.isLt j j.isLt,lookup_complete C k.isLt (by omega) (by omega)]
end Tables
end ThreeSum.LightBandEnumeration
