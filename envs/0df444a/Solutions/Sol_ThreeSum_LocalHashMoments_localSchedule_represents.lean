-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.localSchedule_represents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:52:44.373819+00:00
-- url     : https://prove2.me/submissions/833dc09d-4ed9-4b36-b41b-1159574a1785

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalHashMoments_cover_has_edge
import Theorems.Thm_ThreeSum_LocalHashMoments_localSchedule_covers

set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}
namespace ThreeSum.LocalHashMoments
theorem _root_.solution {h : ℕ} (hh : 0 < h) (a b : LocalField h) :
    ∃ w ∈ localSchedule h, ∃ e : Edge (512 * h) h,
      HashFamily.hashValue w (left e) = a ∧ HashFamily.hashValue w (right e) = b ∧
      HashFamily.bucketSize (leftVertices (512 * h) h) w a ≤ localBucketCap h ∧
      HashFamily.bucketSize (rightVertices (512 * h) h) w b ≤ localBucketCap h := by
  obtain ⟨w, hw, hc⟩ := localSchedule_covers hh (a, b)
  exact ⟨w, hw, cover_has_edge hc⟩
end ThreeSum.LocalHashMoments
