-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.first_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:18.640202+00:00
-- url     : https://prove2.me/submissions/4eeb6a7c-f540-40cf-b7cb-e307e13eee24

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalHashMoments_bucketBound_threshold
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_trimmed_first_moment
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_cross_separated
import Theorems.Thm_ThreeSum_LocalGraph_leftVertices_card
import Theorems.Thm_ThreeSum_LocalGraph_left_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_rightVertices_card
import Theorems.Thm_ThreeSum_LocalGraph_right_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_vertex_sets_separated
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
theorem _root_.solution (hsep : 2 * h < L) (target : K × K) :
    Fintype.card (Edge L h) * Fintype.card (Weight L K) ≤
      2 * Fintype.card K ^ 2 *
        ∑ w, hitCount L h (bucketBound L h (Fintype.card K)) w target := by
  apply HashFamily.trimmed_first_moment left right (cross_separated hsep)
  · intro e u hu
    exact vertex_sets_separated hsep u hu (right e) (right_mem_vertices e)
  · intro e u hu
    exact Ne.symm (vertex_sets_separated hsep (left e) (left_mem_vertices e) u hu)
  · simpa only [leftVertices_card, vertexCount] using
      bucketBound_threshold L h (Fintype.card K) Fintype.card_pos
  · simpa only [rightVertices_card, vertexCount] using
      bucketBound_threshold L h (Fintype.card K) Fintype.card_pos
end ThreeSum.LocalHashMoments
