-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:12.884147+00:00
-- url     : https://prove2.me/submissions/c0263483-64ca-4c53-855c-21997482fbf7

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalHashMoments_bad_partner_bound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_trimmed_second_moment
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_cross_separated
import Theorems.Thm_ThreeSum_LocalGraph_edge_card
import Theorems.Thm_ThreeSum_LocalGraph_endpoint_injective
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
theorem _root_.solution (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (target : K × K) (B : ℕ) :
    Fintype.card K ^ 2 * (∑ w, hitCount L h B w target ^ 2) ≤
      5 * Fintype.card (Edge L h) * Fintype.card (Weight L K) := by
  apply HashFamily.trimmed_second_moment left right endpoint_injective
    (cross_separated hsep) (2 * degree L h + groupSize h) bad_partner_bound
  · omega
  · simpa only [edge_card, outputCount, groupSize] using hE
end ThreeSum.LocalHashMoments
