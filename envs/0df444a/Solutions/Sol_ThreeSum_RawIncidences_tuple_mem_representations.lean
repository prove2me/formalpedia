-- Prove2me | solution 1 for ThreeSum.RawIncidences.tuple_mem_representations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:19:11.678913+00:00
-- url     : https://prove2.me/submissions/cbb9de2e-b525-4450-ab05-370813a58d50

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8
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
theorem _root_.solution {h J : ℕ} (t : ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ representations h J b c ↔
      globalModulus h J ∣ b - tupleLeft t ∧ globalModulus h J ∣ c - tupleRight t := by
  rw [mem_representations]
  simp only [List.length_ofFn, true_and, tupleLeft, tupleRight]
end ThreeSum.RawIncidences
