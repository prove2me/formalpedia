-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.schedule_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:23.544794+00:00
-- url     : https://prove2.me/submissions/31ed2108-a596-4aae-a44f-91ec4faeea03

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_WeightedCache3SUM_Alias_a70ba715862c7181
import Theorems.Thm_ThreeSum_LocalHashMoments_mem_allWeights
import Definitions.Def_WeightedCache3SUM_Alias_01bae1d392eb872f
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
theorem _root_.solution (values : List K) (hvalues : ∀ x, x ∈ values)
    (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (hupper : Fintype.card K ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    ∃ w ∈ schedule L h values,
      Covers L h (bucketBound L h (Fintype.card K)) w target := by
  have hfreq : ∀ u ∈ (univ : Finset (K × K)), Fintype.card (Weight L K) ≤
      (320 * (2 * h + 1)) * (univ.filter fun w =>
        Covers L h (bucketBound L h (Fintype.card K)) w u).card := by
    intro u hu
    exact cover_frequency hsep hDelta hG hE hupper u
  have hc := Cover.greedy_cover (allWeights L values) (mem_allWeights values hvalues)
    (Covers L h (bucketBound L h (Fintype.card K)))
    (univ : Finset (K × K)) (320 * (2 * h + 1)) (by omega) hfreq target (mem_univ _)
  simpa only [schedule, scheduleLength, Finset.card_univ, Fintype.card_prod, pow_two] using hc
end ThreeSum.LocalHashMoments
