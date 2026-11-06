-- Prove2me | solution 1 for QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegion_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:12:56.627418+00:00
-- url     : https://prove2.me/submissions/6f9661b6-bdbe-49af-bbf0-92f0b7d7ec00

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace EdgeRestrictedStoppedRecursion
theorem _root_.solution
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) (x y : ι) :
    (x, y) ∈ tree.edgeRegion owner ↔ (y, x) ∈ tree.edgeRegion owner := by
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      exact hsymmetric x y
  | split hsubset hsymmetric hincident hpartition hminimum hleft hright
      leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner => exact ihLeft owner
      | inr owner => exact ihRight owner
end EdgeRestrictedStoppedRecursion
end QEC.Locality
