-- Prove2me | solution 1 for QEC.Locality.BGKLSeparatorSplit.vertices_subset_children_union_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:19.380014+00:00
-- url     : https://prove2.me/submissions/e5d1db70-0df2-441b-9d75-9e4ee9e3a40f

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
namespace BGKLSeparatorSplit
theorem _root_.solution
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    vertices ⊆ (split.left ∪ split.right) ∪ split.separator := by
  intro q hq
  by_cases hqSeparator : q ∈ split.separator
  · exact Finset.mem_union_right _ hqSeparator
  · apply Finset.mem_union_left
    rw [split.partition]
    exact Finset.mem_sdiff.mpr ⟨hq, hqSeparator⟩
end BGKLSeparatorSplit
end QEC.Locality
