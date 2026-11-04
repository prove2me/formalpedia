-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.hitCount_cap_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:25:25.163743+00:00
-- url     : https://prove2.me/submissions/4f385d66-5585-4928-8869-7f6635c9dbd2

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_endpoint_injective
import Theorems.Thm_ThreeSum_LocalGraph_left_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_right_mem_vertices
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
theorem _root_.solution (B : ℕ) (w : Weight L K) (target : K × K) :
    hitCount L h B w target ≤ B ^ 2 := by
  classical
  let F : Finset (Edge L h) := univ.filter (fun e => w ∈
    HashFamily.trimmedPairEvent (left e) (right e) target.1 target.2
      (leftVertices L h) (rightVertices L h) B)
  change F.card ≤ B ^ 2
  by_cases hz : F.card = 0
  · simp only [hz, Nat.zero_le]
  have hn : F.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  obtain ⟨e, he⟩ := hn
  have hlight : HashFamily.bucketSize (leftVertices L h) w target.1 ≤ B ∧
      HashFamily.bucketSize (rightVertices L h) w target.2 ≤ B :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp he).2).2
  let VL := (leftVertices L h).filter (fun s => HashFamily.hashValue w s = target.1)
  let VR := (rightVertices L h).filter (fun s => HashFamily.hashValue w s = target.2)
  have hcount : F.card ≤ (VL ×ˢ VR).card := by
    apply Finset.card_le_card_of_injOn (fun e : Edge L h => (left e, right e))
    · intro f hf
      have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).2).1
      have hv : HashFamily.hashValue w (left f) = target.1 ∧
          HashFamily.hashValue w (right f) = target.2 := (Finset.mem_filter.mp hh).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨left_mem_vertices f, hv.1⟩,
         Finset.mem_filter.mpr ⟨right_mem_vertices f, hv.2⟩⟩
    · intro e he f hf hef
      exact endpoint_injective hef
  calc
    F.card ≤ VL.card * VR.card := by simpa only [Finset.card_product] using hcount
    _ ≤ B * B := Nat.mul_le_mul hlight.1 hlight.2
    _ = B ^ 2 := by rw [pow_two]
end ThreeSum.LocalHashMoments
