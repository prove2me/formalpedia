-- Prove2me | solution 1 for QEC.Locality.BGKLSeparatorSplit.children_decoupled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:20.191013+00:00
-- url     : https://prove2.me/submissions/30edecc4-0426-4e1d-bbd9-39343e5fbde2

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
    P.fixedGeneratorDecoupled (split.left : Set ι) (split.right : Set ι) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro q hqLeft hqRight
    exact (Finset.disjoint_left.mp split.disjoint) hqLeft hqRight
  · intro p hp q hq
    exact split.noEdge hp hq
end BGKLSeparatorSplit
end QEC.Locality
