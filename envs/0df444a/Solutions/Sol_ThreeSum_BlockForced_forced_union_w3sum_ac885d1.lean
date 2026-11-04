-- Prove2me | solution 1 for ThreeSum.BlockForced.forced_union_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:30:18.958385+00:00
-- url     : https://prove2.me/submissions/28667027-f8d1-4dc4-ad67-e05c2f4044d5

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
import Theorems.Thm_ThreeSum_BlockRows_flat_row
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
import Theorems.Thm_ThreeSum_BlockRows_mem_join
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_BlockRows_row_flat
import Theorems.Thm_ThreeSum_BlockRows_row_inter
import Theorems.Thm_ThreeSum_BlockRows_row_join
import Theorems.Thm_ThreeSum_BlockRows_row_sdiff
import Theorems.Thm_ThreeSum_BlockRows_row_union
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BlockEncoding.leftSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.rightSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.row_leftSubset
attribute [local simp] ThreeSum.BlockEncoding.row_outputSubset
attribute [local simp] ThreeSum.BlockEncoding.row_rightSubset
attribute [local simp] ThreeSum.BlockRows.flat_row
attribute [local simp] ThreeSum.BlockRows.mem_flat
attribute [local simp] ThreeSum.BlockRows.mem_join
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.BlockRows.mem_row
attribute [local simp] ThreeSum.BlockRows.row_flat
attribute [local simp] ThreeSum.BlockRows.row_inter
attribute [local simp] ThreeSum.BlockRows.row_join
attribute [local simp] ThreeSum.BlockRows.row_sdiff
attribute [local simp] ThreeSum.BlockRows.row_union
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


namespace ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
section FiniteRows
variable {J L : ℕ}
private theorem suffix_not_prefix {I : Finset (Fin J)} {Q : Fin J → Finset (Fin L)}
    {x : Finset (Coord J L)} (hx : x ⊆ remaining I Q) {i : Fin J} (hi : i ∈ I)
    (a : Fin L) : Sigma.mk i a ∉ x := by
  intro ha
  exact (Finset.mem_compl.mp (mem_join.mp (hx ha)).1) hi
end FiniteRows
section WeightedCounts
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
end WeightedCounts
end ThreeSum.BlockForced
set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
variable {J L : ℕ}
namespace ThreeSum.BlockForced
theorem _root_.solution (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ I, u i ⊆ Q i) (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) :
    (prefixLeft I u ∪ x) ∪ (prefixRight I Q u ∪ (remaining I Q \ x)) = flat Q := by
  ext ⟨i, a⟩
  by_cases hi : i ∈ I
  · have hn := suffix_not_prefix hx hi a
    have hs := hu i hi
    simp only [prefixLeft, prefixRight, remaining, mem_join, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_compl, mem_flat, hi, not_true_eq_false,
      true_and, false_and, or_false, false_or, hn]
    constructor
    · rintro (ha | ⟨ha, _⟩)
      · exact hs ha
      · exact ha
    · intro ha
      by_cases hau : a ∈ u i
      · exact Or.inl hau
      · exact Or.inr ⟨ha, hau⟩
  · have hs : Sigma.mk i a ∈ x → a ∈ Q i := fun ha => (mem_join.mp (hx ha)).2
    simp only [prefixLeft, prefixRight, remaining, mem_join, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_compl, mem_flat, hi, not_false_eq_true,
      true_and, false_and, or_false, false_or]
    constructor
    · rintro (ha | ⟨ha, _⟩)
      · exact hs ha
      · exact ha
    · intro ha
      by_cases hax : Sigma.mk i a ∈ x
      · exact Or.inl hax
      · exact Or.inr ⟨ha, hax⟩
end ThreeSum.BlockForced
