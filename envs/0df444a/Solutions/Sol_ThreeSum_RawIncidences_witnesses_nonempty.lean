-- Prove2me | solution 1 for ThreeSum.RawIncidences.witnesses_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:02:50.030984+00:00
-- url     : https://prove2.me/submissions/2820f50d-e4c1-4ffe-b0c7-6dfa3eb8c8c9

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_lift_complete
import Theorems.Thm_ThreeSum_RawIncidences_ofFn_tupleOfList
import Theorems.Thm_ThreeSum_RawIncidences_tuple_difference_congruence
import Theorems.Thm_ThreeSum_RawIncidences_mem_witnesses
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Definitions.Def_WeightedCache3SUM_Alias_088f5813e7c1796a
import Theorems.Thm_ThreeSum_GlobalEncoding_representations_nonempty
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8
import Theorems.Thm_ThreeSum_Radix_representations_nonempty
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} {P d a b c : ℤ}
    (hh : 0 < h) (hP : 0 < P) (hdiv : P ∣ c - b - a) :
    (witnesses h J P d a b c).Nonempty := by
  have heq : Int.ModEq P (c % P - b % P - a % P) (c - b - a) :=
    ((Int.mod_modEq c P).sub (Int.mod_modEq b P)).sub (Int.mod_modEq a P)
  have hnorm : P ∣ c % P - b % P - a % P := heq.dvd_iff.mpr hdiv
  obtain ⟨j, hj, he⟩ := Arithmetic.small_lift_exists hP
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP) hnorm
  obtain ⟨l, hl⟩ := lift_complete hj
  obtain ⟨xs, hxs⟩ := representations_nonempty hh J (b % P) (c % P + d)
  let hlen := ((mem_representations h J (b % P) (c % P + d) xs).mp hxs).1
  let t := tupleOfList xs hlen
  have ht : List.ofFn t ∈ representations h J (b % P) (c % P + d) := by
    simpa only [t, ofFn_tupleOfList] using hxs
  refine ⟨(t, l), mem_witnesses.mpr ⟨ht, ?_⟩⟩
  have hd := tuple_difference_congruence ht
  have htarget : a % P + lift l * P + d = (c % P + d) - b % P := by
    rw [hl]
    linarith
  simpa only [htarget] using hd
end ThreeSum.RawIncidences
