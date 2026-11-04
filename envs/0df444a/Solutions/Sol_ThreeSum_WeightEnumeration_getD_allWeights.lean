-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.getD_allWeights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:56:49.132261+00:00
-- url     : https://prove2.me/submissions/cc37988b-9e06-4e36-a362-6265e2160269

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Theorems.Thm_ThreeSum_WeightEnumeration_getElem_allWeights

set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]
namespace ThreeSum.WeightEnumeration
theorem _root_.solution (L p k : ℕ) (fallback : Weight L K) (hk : k < p^(2*L)) :
    (allWeights L ((List.range p).map (fun n : ℕ => (n : K)))).getD k fallback =
      decodedWeight (K := K) L p k := by
  rw [List.getD_eq_getElem _ _ (by rw [allWeights_length]; exact hk)]
  exact getElem_allWeights L p k hk
end ThreeSum.WeightEnumeration
