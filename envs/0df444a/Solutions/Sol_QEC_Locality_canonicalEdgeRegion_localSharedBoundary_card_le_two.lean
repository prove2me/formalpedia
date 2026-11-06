-- Prove2me | solution 1 for QEC.Locality.canonicalEdgeRegion_localSharedBoundary_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:27:53.178288+00:00
-- url     : https://prove2.me/submissions/e488f28d-43a5-4fc0-ba7e-8a986fc04f26

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Theorems.Thm_QEC_Locality_canonicalEdgeRegion_incident_card_le_two
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (owner : ι × ι) :
    ((edgeIncidentVertices (canonicalEdgeRegion G owner)) ∩
      edgeDivisionSharedBoundary (canonicalEdgeRegion G)
        (canonicalEdgeRepresentatives G)).card ≤ 2 := by
  classical
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (canonicalEdgeRegion_incident_card_le_two G owner)
end QEC.Locality
