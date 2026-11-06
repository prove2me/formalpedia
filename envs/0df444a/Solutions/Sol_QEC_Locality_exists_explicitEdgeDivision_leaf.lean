-- Prove2me | solution 1 for QEC.Locality.exists_explicitEdgeDivision_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:13:44.313687+00:00
-- url     : https://prove2.me/submissions/cd1d570c-3513-4245-8bfa-f8e723f8b94d

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Theorems.Thm_QEC_Locality_canonicalEdgeRegions_isEdgeDivision
import Theorems.Thm_QEC_Locality_canonicalEdgeRegion_incident_card_le
import Theorems.Thm_QEC_Locality_canonicalEdgeRegion_localSharedBoundary_card_le_two
import Theorems.Thm_QEC_Locality_canonicalEdgeRepresentatives_card_le_directedEdges

set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (G : ConnectivityGraph ι)
    {r : Nat} (hr : 2 ≤ r) :
    ∃ regions : (ι × ι) → Finset (ι × ι), ∃ active : Finset (ι × ι),
      IsEdgeDivision G regions active ∧
        (∀ owner, owner ∈ active →
          (edgeIncidentVertices (regions owner)).card ≤ r) ∧
        (∀ owner, owner ∈ active →
          ((edgeIncidentVertices (regions owner)) ∩
            edgeDivisionSharedBoundary regions active).card ≤ 2) ∧
        active.card ≤ (directedEdgeFinset G).card := by
  classical
  exact ⟨canonicalEdgeRegion G, canonicalEdgeRepresentatives G,
    canonicalEdgeRegions_isEdgeDivision G,
    fun owner _ => canonicalEdgeRegion_incident_card_le G hr owner,
    fun owner _ => canonicalEdgeRegion_localSharedBoundary_card_le_two G owner,
    canonicalEdgeRepresentatives_card_le_directedEdges G⟩
end QEC.Locality
