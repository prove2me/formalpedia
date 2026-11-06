-- Prove2me | solution 1 for QEC.Locality.totalEdgeRegion_incident_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:26:20.783227+00:00
-- url     : https://prove2.me/submissions/c68ec769-06b3-43d6-b212-28932fb788ed

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Theorems.Thm_QEC_Locality_totalEdgeRegion_incident_card_le_vertexCount
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (G : ConnectivityGraph ι)
    {r : Nat} (hr : Fintype.card ι ≤ r) :
    (edgeIncidentVertices (totalEdgeRegion G ())).card ≤ r :=
  (totalEdgeRegion_incident_card_le_vertexCount G).trans hr
end QEC.Locality
