-- Prove2me | solution 1 for QEC.Locality.ExplicitProfileEdgeDivision.isolated_not_mem_incident
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:01:23.775638+00:00
-- url     : https://prove2.me/submissions/d306acb7-2db1-4dec-a36a-47d86809c1de

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff
import Theorems.Thm_QEC_Locality_mem_edgeIncidentVertices_iff
import Theorems.Thm_QEC_Locality_mem_graphIsolatedVertices_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace ExplicitProfileEdgeDivision
theorem _root_.solution
    {G : ConnectivityGraph ι} {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap)
    {x : ι} (hx : x ∈ graphIsolatedVertices G)
    (owner : division.Owner) (howner : owner ∈ division.active) :
    x ∉ edgeIncidentVertices (division.region owner) := by
  letI : DecidableEq division.Owner := division.ownerDecidableEq
  intro hxIncident
  rcases (mem_edgeIncidentVertices_iff (division.region owner) x).1 hxIncident with
    ⟨⟨a, b⟩, habRegion, hxa | hxb⟩
  · have hab : G.adjacent a b := (mem_directedEdgeFinset_iff G a b).1
      (division.isEdgeDivision.1 owner howner habRegion)
    exact (mem_graphIsolatedVertices_iff G x).1 hx b (hxa.symm ▸ hab)
  · have hba : G.adjacent b a := G.symmetric ((mem_directedEdgeFinset_iff G a b).1
      (division.isEdgeDivision.1 owner howner habRegion))
    exact (mem_graphIsolatedVertices_iff G x).1 hx a (hxb.symm ▸ hba)
end ExplicitProfileEdgeDivision
end QEC.Locality
