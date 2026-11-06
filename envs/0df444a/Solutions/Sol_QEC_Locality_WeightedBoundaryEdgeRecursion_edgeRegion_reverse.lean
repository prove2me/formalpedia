-- Prove2me | solution 1 for QEC.Locality.WeightedBoundaryEdgeRecursion.edgeRegion_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:42:22.575625+00:00
-- url     : https://prove2.me/submissions/f228a00d-c7eb-42c5-9aa7-5ca01920dc5b

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
    (owner : tree.edgeOwnerType) (x y : ι) :
    (x, y) ∈ tree.edgeRegion owner ↔ (y, x) ∈ tree.edgeRegion owner := by
  induction tree with
  | leaf _ hsymmetric _ _ _ _ => exact hsymmetric x y
  | split _ _ _ _ _ spine _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner => exact ihFirst owner
      | inr owner =>
          cases owner with
          | inl owner => exact ihSecond owner
          | inr owner => exact ihThird owner
end WeightedBoundaryEdgeRecursion
end QEC.Locality
