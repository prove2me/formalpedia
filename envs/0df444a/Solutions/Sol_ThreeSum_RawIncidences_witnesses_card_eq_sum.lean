-- Prove2me | solution 1 for ThreeSum.RawIncidences.witnesses_card_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:16.343317+00:00
-- url     : https://prove2.me/submissions/48fc0eb7-1dac-4d67-89ba-0d5dad0d824a

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_tuple_mem_representations
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
theorem _root_.solution (h J : ℕ) (P d a b c : ℤ) :
    (witnesses h J P d a b c).card =
      ∑ t : ChoiceTuple h J, ∑ j : Fin 3,
        if globalModulus h J ∣ b % P - tupleLeft t ∧
          globalModulus h J ∣ c % P + d - tupleRight t ∧
          globalModulus h J ∣ (a % P + lift j * P + d) - tupleKey t
        then 1 else 0 := by
  rw [witnesses, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [tuple_mem_representations, and_assoc]
end ThreeSum.RawIncidences
