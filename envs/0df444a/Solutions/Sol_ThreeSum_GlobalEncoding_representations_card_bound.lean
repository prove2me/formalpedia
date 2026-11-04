-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.representations_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:26:07.131242+00:00
-- url     : https://prove2.me/submissions/f56b205e-bf98-41f2-b5f6-19c30d2d2ff3

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_localFiber_card_bound
import Definitions.Def_WeightedCache3SUM_Alias_8a1bc378764c1bfd


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution (h J : ℕ) (a b : ℤ) :
    (representations h J a b).card ≤ representationCap h J :=
  Radix.representations_card_le (localPrime h) rawLeft rawRight
    (scheduleSize h * localBucketCap h ^ 2) (localFiber_card_bound h) J a b
end ThreeSum.GlobalEncoding
