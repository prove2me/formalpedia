-- Prove2me | solution 1 for QEC.Locality.complement_interiors_subset_sharedBoundary_union_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:25:39.785809+00:00
-- url     : https://prove2.me/submissions/03360307-b9ab-49cb-918d-4ec080f7b43e

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_vertices_subset_interiors_union_sharedBoundary_union_isolated

set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {m : Type w} [DecidableEq m] {G : ConnectivityGraph ι}
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision G regions active) :
    Finset.univ \ (active.biUnion fun i => edgeDivisionInterior regions active i) ⊆
      edgeDivisionSharedBoundary regions active ∪ graphIsolatedVertices G := by
  intro x hx
  have hcover := vertices_subset_interiors_union_sharedBoundary_union_isolated hDivision
    (Finset.mem_univ x)
  rcases Finset.mem_union.mp hcover with hInteriorOrShared | hIsolated
  · rcases Finset.mem_union.mp hInteriorOrShared with hInterior | hShared
    · exact (Finset.mem_sdiff.mp hx).2 hInterior |>.elim
    · exact Finset.mem_union_left _ hShared
  · exact Finset.mem_union_right _ hIsolated
end QEC.Locality
