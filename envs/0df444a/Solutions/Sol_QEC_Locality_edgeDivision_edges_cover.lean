-- Prove2me | solution 1 for QEC.Locality.edgeDivision_edges_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:13:22.891604+00:00
-- url     : https://prove2.me/submissions/760760f9-f07d-45d9-ae68-a09be1c7a9c3

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision

set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active) :
    active.biUnion regions = directedEdgeFinset G := by
  classical
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_biUnion.mp hedge with ⟨i, hi, hiedge⟩
    exact hDivision.1 i hi hiedge
  · intro hedge
    rcases hDivision.2.2 edge hedge with ⟨i, ⟨hi, hiedge⟩, _⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, hiedge⟩
end QEC.Locality
