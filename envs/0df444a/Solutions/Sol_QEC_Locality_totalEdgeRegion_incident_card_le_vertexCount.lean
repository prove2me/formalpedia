-- Prove2me | solution 1 for QEC.Locality.totalEdgeRegion_incident_card_le_vertexCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:23:50.876029+00:00
-- url     : https://prove2.me/submissions/6d71f6eb-fdb6-414c-a0ee-d190349ff6e3

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision

set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (G : ConnectivityGraph ι) :
    (edgeIncidentVertices (totalEdgeRegion G ())).card ≤ Fintype.card ι := by
  classical
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)
end QEC.Locality
