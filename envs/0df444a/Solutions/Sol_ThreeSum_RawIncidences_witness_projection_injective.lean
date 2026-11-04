-- Prove2me | solution 1 for ThreeSum.RawIncidences.witness_projection_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:04.778343+00:00
-- url     : https://prove2.me/submissions/119c7246-6bef-40de-965e-6d4162462cba

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_lift_small
import Theorems.Thm_ThreeSum_RawIncidences_lift_injective
import Theorems.Thm_ThreeSum_RawIncidences_mem_witnesses
import Theorems.Thm_ThreeSum_Arithmetic_guarded_lift_unique
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
theorem _root_.solution {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    Set.InjOn (fun w : Witness h J => List.ofFn w.1) (witnesses h J P d a b c) := by
  intro w hw v hv he
  have ht : w.1 = v.1 := List.ofFn_injective he
  have hwq := (mem_witnesses.mp hw).2
  have hvq := (mem_witnesses.mp hv).2
  have hd : globalModulus h J ∣
      (a % P + lift w.2 * P + d) - (a % P + lift v.2 * P + d) := by
    rw [ht] at hwq
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hwq hvq
  have hj := Arithmetic.guarded_lift_unique hP hguard (lift_small w.2) (lift_small v.2) hd
  exact Prod.ext ht (lift_injective hj)
end ThreeSum.RawIncidences
