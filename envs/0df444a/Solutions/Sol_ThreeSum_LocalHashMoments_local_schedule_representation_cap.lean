-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.local_schedule_representation_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:48.256363+00:00
-- url     : https://prove2.me/submissions/772a15da-f75b-4a6f-bdb7-170046551be7

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalHashMoments_localSchedule_length
import Theorems.Thm_ThreeSum_LocalHashMoments_local_representation_cap
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}
namespace ThreeSum.LocalHashMoments
theorem _root_.solution (h : ℕ) (target : LocalField h × LocalField h) :
    ((localSchedule h).map (fun w => hitCount (512 * h) h (localBucketCap h) w target)).sum ≤
      (320 * (2 * h + 1) * (Nat.log2 (localPrime h ^ 2) + 1)) * localBucketCap h ^ 2 := by
  have hs : ∀ ws : List (Weight (512 * h) (LocalField h)),
      (ws.map (fun w => hitCount (512 * h) h (localBucketCap h) w target)).sum ≤
        ws.length * localBucketCap h ^ 2 := by
    intro ws
    induction ws with
    | nil => simp
    | cons w ws ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hw := local_representation_cap h w target
      nlinarith
  simpa only [localSchedule_length] using hs (localSchedule h)
end ThreeSum.LocalHashMoments
