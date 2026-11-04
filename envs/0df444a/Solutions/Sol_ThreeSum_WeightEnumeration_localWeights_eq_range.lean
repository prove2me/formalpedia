-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.localWeights_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:47:20.453635+00:00
-- url     : https://prove2.me/submissions/4304abda-b198-45c0-9444-a6ba8fa77aa0

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]
namespace ThreeSum.WeightEnumeration
theorem _root_.solution (h : ℕ) :
    allWeights (512*h) (localValues h) =
      (List.range ((LocalCoverBounds.localPrime h)^(2*(512*h)))).map
        (decodedWeight (K := LocalField h) (512*h) (LocalCoverBounds.localPrime h)) := by
  exact allWeights_eq_range _ _
end ThreeSum.WeightEnumeration
