-- Prove2me | solution 1 for QEC.Locality.canonicalEdgeRegion_incident_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:27:42.404742+00:00
-- url     : https://prove2.me/submissions/c9ad8fde-589d-419c-ac7f-9055674b0a0c

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
    (G : ConnectivityGraph ι) {r : Nat} (hr : 2 ≤ r) (owner : ι × ι) :
    (edgeIncidentVertices (canonicalEdgeRegion G owner)).card ≤ r :=
  (canonicalEdgeRegion_incident_card_le_two G owner).trans hr
end QEC.Locality
