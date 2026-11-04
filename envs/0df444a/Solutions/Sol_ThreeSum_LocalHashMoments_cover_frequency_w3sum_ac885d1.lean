-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.cover_frequency_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:05.914462+00:00
-- url     : https://prove2.me/submissions/49132683-025a-4943-9cb5-7d06ddf5a576

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Theorems.Thm_ThreeSum_LocalHashMoments_first_moment_real
import Theorems.Thm_ThreeSum_LocalHashMoments_second_moment_real
import Theorems.Thm_ThreeSum_Cover_trimmed_support_fraction
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_e9faaede4c647b1a
import Theorems.Thm_ThreeSum_LocalCoverBounds_mean_positive
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
    (hupper : Fintype.card K ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    Fintype.card (Weight L K) ≤ 320 * (2 * h + 1) *
      (univ.filter fun w => Covers L h (bucketBound L h (Fintype.card K)) w target).card := by
  have hl := mean_lower (Nat.le_of_lt hsep) (p := Fintype.card K)
    Fintype.card_pos hupper
  have hm : 0 < mean L h (Fintype.card K) :=
    mean_positive (Nat.le_of_lt hsep) Fintype.card_pos
  have hscale : 1 ≤ 16 * (2 * h + 1 : ℝ) * mean L h (Fintype.card K) := by
    have hd : (0 : ℝ) < 16 * (2 * (h : ℝ) + 1) := by positivity
    have ht := (div_le_iff₀ hd).mp hl
    nlinarith
  have hs := Cover.trimmed_support_fraction
    (fun w => (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ))
    (2 * h) hm (by simpa using hscale)
    (first_moment_real hsep target)
    (second_moment_real hsep hDelta hG hE target _)
  have hf : (univ.filter fun w =>
      (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) ≠ 0) =
      (univ.filter fun w => Covers L h (bucketBound L h (Fintype.card K)) w target) := by
    apply Finset.filter_congr
    intro w hw
    change (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) ≠ 0 ↔
      hitCount L h (bucketBound L h (Fintype.card K)) w target ≠ 0
    exact Nat.cast_ne_zero
  rw [hf] at hs
  exact_mod_cast hs
end ThreeSum.LocalHashMoments
