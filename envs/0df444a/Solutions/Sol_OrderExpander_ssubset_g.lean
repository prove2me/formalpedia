-- Prove2me | solution 1 for OrderExpander.ssubset_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:45:31.485992+00:00
-- url     : https://prove2.me/submissions/8a74c36f-dd00-4f62-8ccf-29085bacecec

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]
namespace OrderExpander
theorem _root_.solution {S C : Set α} (GC : Good C) (prseg : S ⊏ C) : S ⊂ g S :=
  ssubset_of_IsPropSegment (GC.2 prseg).1
end OrderExpander
