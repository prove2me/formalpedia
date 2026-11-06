-- Prove2me | solution 1 for QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegion_incident_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:41:49.622376+00:00
-- url     : https://prove2.me/submissions/67fb516f-a314-42ad-bcd0-ab8fbd61d652

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace EdgeRestrictedStoppedRecursion
theorem _root_.solution
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)).card ≤ r := by
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      exact (Finset.card_le_card hincident).trans hcard
  | split hsubset hsymmetric hincident hpartition hminimum hleft hright
      leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner => exact ihLeft owner
      | inr owner => exact ihRight owner
end EdgeRestrictedStoppedRecursion
end QEC.Locality
