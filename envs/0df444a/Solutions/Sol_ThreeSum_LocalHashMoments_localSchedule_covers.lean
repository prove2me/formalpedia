-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.localSchedule_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:44.512503+00:00
-- url     : https://prove2.me/submissions/73178d57-4617-4ee4-b9de-f3c95ba88445

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalHashMoments_schedule_covers
import Theorems.Thm_ThreeSum_LocalHashMoments_mem_localValues
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalCoverBounds_degree_lt_localPrime
import Theorems.Thm_ThreeSum_LocalCoverBounds_edgeCount_le_localPrime_sq
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lt_localPrime
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_upper
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
theorem _root_.solution {h : ℕ} (hh : 0 < h) (target : LocalField h × LocalField h) :
    ∃ w ∈ localSchedule h, Covers (512 * h) h (localBucketCap h) w target := by
  have hs := schedule_covers (localValues h) (mem_localValues h)
    (L := 512 * h) (h := h) (by omega)
    (by simpa only [ZMod.card] using (degree_lt_localPrime hh).le)
    (by simpa only [ZMod.card] using (groupSize_lt_localPrime hh).le)
    (by simpa only [ZMod.card] using edgeCount_le_localPrime_sq h)
    (by simpa only [ZMod.card] using localPrime_sq_upper h) target
  simpa only [localSchedule, bucketBound, localBucketCap, ZMod.card] using hs
end ThreeSum.LocalHashMoments
