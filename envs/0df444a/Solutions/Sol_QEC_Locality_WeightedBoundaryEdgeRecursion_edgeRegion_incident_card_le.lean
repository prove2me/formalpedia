-- Prove2me | solution 1 for QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegion_incident_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:43:36.27297+00:00
-- url     : https://prove2.me/submissions/7c374ece-d6ed-42a1-913f-b629b300dc85

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace WeightedBoundaryEdgeRecursion
theorem _root_.solution
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)).card ≤ r := by
  induction tree with
  | leaf _ _ hincident _ hcard _ =>
      exact (Finset.card_le_card hincident).trans hcard
  | split _ _ _ _ _ spine _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner => exact ihFirst owner
      | inr owner =>
          cases owner with
          | inl owner => exact ihSecond owner
          | inr owner => exact ihThird owner
end WeightedBoundaryEdgeRecursion
end QEC.Locality
