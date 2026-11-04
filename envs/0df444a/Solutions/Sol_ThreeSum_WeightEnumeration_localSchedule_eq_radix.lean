-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.localSchedule_eq_radix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:56:45.500176+00:00
-- url     : https://prove2.me/submissions/5e1624ac-b439-4230-9122-15506b23294c

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Theorems.Thm_ThreeSum_WeightEnumeration_localWeights_eq_range

set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]
namespace ThreeSum.WeightEnumeration
theorem _root_.solution (h : ℕ) :
    localSchedule h =
      Cover.greedyChoices
        ((List.range ((LocalCoverBounds.localPrime h)^(2*(512*h)))).map
          (decodedWeight (K := LocalField h) (512*h) (LocalCoverBounds.localPrime h)))
        (Covers (512*h) h (bucketBound (512*h) h (Fintype.card (LocalField h))))
        (Finset.univ : Finset (LocalField h × LocalField h))
        (scheduleLength h (Fintype.card (LocalField h))) := by
  unfold localSchedule schedule
  rw [localWeights_eq_range]
end ThreeSum.WeightEnumeration
