-- Prove2me | solution 1 for QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeRegion_incident_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:48:06.364736+00:00
-- url     : https://prove2.me/submissions/d9befa9b-b403-450d-b8ec-cc775d3724b9

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_incident_card_le
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_incident_card_le


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace EdgeRestrictedStoppedRecursion
theorem _root_.solution
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    (edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile owner)).card ≤ r :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).edgeRegion_incident_card_le owner.2
end EdgeRestrictedStoppedRecursion
end QEC.Locality
