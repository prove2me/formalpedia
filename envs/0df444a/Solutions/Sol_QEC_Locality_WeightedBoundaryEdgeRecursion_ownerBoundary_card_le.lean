-- Prove2me | solution 1 for QEC.Locality.WeightedBoundaryEdgeRecursion.ownerBoundary_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:42:53.851943+00:00
-- url     : https://prove2.me/submissions/067ef8c9-4b91-4fba-b43d-f7d63d99d842

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement

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
    (tree.ownerBoundary owner).card ≤ 6 * spineBudget := by
  induction tree with
  | leaf _ _ _ _ _ hboundaryCard => exact hboundaryCard
  | split _ _ _ _ _ spine _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner => exact ihFirst owner
      | inr owner =>
          cases owner with
          | inl owner => exact ihSecond owner
          | inr owner => exact ihThird owner
end WeightedBoundaryEdgeRecursion
end QEC.Locality
