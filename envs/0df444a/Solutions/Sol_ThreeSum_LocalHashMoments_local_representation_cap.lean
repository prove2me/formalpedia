-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.local_representation_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:40.541219+00:00
-- url     : https://prove2.me/submissions/df1bd303-f7e1-4b02-934c-732bd8e60691

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_WeightedCache3SUM_Alias_c2fc45f3d7e81d20

set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}
namespace ThreeSum.LocalHashMoments
theorem _root_.solution (h : ℕ) (w : Weight (512 * h) (LocalField h))
    (target : LocalField h × LocalField h) :
    hitCount (512 * h) h (localBucketCap h) w target ≤ localBucketCap h ^ 2 :=
  hitCount_cap _ _ _
end ThreeSum.LocalHashMoments
