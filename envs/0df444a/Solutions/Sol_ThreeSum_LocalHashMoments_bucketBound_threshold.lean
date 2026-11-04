-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.bucketBound_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:25:24.009542+00:00
-- url     : https://prove2.me/submissions/1354064f-a131-43af-b0f5-f2dcfe7846a3

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalCoverBounds_bucketCap_threshold


set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}
namespace ThreeSum.LocalHashMoments
theorem _root_.solution (L h p : ℕ) (hp : 0 < p) :
    4 * (p + vertexCount L h) ≤ bucketBound L h p * p := by
  exact bucketCap_threshold hp
end ThreeSum.LocalHashMoments
