-- Prove2me | solution 1 for ThreeSum.RawIncidences.witness_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:11.900626+00:00
-- url     : https://prove2.me/submissions/b2d73b13-1f2e-4d4c-bf10-07f0741bc8aa

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_lift_small
import Theorems.Thm_ThreeSum_RawIncidences_tuple_difference_congruence
import Theorems.Thm_ThreeSum_RawIncidences_mem_witnesses
import Theorems.Thm_ThreeSum_Arithmetic_guarded_remainder_lift_sound
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
theorem _root_.solution {h J : ℕ} {P d a b c : ℤ} {w : Witness h J}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hw : w ∈ witnesses h J P d a b c) : P ∣ c - b - a := by
  obtain ⟨hrep, hquery⟩ := mem_witnesses.mp hw
  have hdiff := tuple_difference_congruence hrep
  have hkey : Int.ModEq (globalModulus h J)
      (a % P + lift w.2 * P + d) (c % P + d - b % P) := by
    apply Int.modEq_of_dvd
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hdiff hquery
  exact Arithmetic.guarded_remainder_lift_sound hP hguard (lift_small w.2) hkey
end ThreeSum.RawIncidences
