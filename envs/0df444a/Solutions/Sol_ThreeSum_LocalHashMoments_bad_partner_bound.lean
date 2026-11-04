-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.bad_partner_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:12.195526+00:00
-- url     : https://prove2.me/submissions/e4a90b85-2780-486d-a4e5-b62c5e6458d7

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_WeightedCache3SUM_Alias_4e842a77daeb59cb
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_endpoint_fiber_bounds
import Theorems.Thm_ThreeSum_LocalGraph_mask_fiber_bound
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
theorem _root_.solution (e : Edge L h) :
    (HashFamily.badPartners left right e).card ≤ 2 * degree L h + groupSize h := by
  apply HashFamily.badPartners_card_le
  · simpa only [eq_comm, degree] using (endpoint_fiber_bounds e).1
  · simpa only [eq_comm, degree] using (endpoint_fiber_bounds e).2
  · change (univ.filter (fun f : Edge L h =>
      (fun i => left e i == right e i) = (fun i => left f i == right f i))).card ≤
      (2 * h).choose h
    simpa only [eq_comm] using mask_fiber_bound e
end ThreeSum.LocalHashMoments
