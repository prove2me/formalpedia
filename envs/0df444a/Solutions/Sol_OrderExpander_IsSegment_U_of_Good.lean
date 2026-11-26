-- Prove2me | solution 1 for OrderExpander.IsSegment_U_of_Good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:47:04.279533+00:00
-- url     : https://prove2.me/submissions/c2862099-840d-4006-9ca2-75395fbd3b20

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_OrderExpander_comparability

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open OrderExpander
variable [PartialOrder α] [OrderExpander α]
namespace OrderExpander
theorem _root_.solution {D : Set α} (goodD : Good D) : D ⊑ U := by
  constructor
  · intro x hx
    exact ⟨D, goodD, hx⟩
  · intro c c_in_U d d_in_D c_le_d
    obtain ⟨C, Good_C⟩ := c_in_U
    rcases comparability C D Good_C.1 goodD with CsegD | DsegC
    · exact CsegD.1 Good_C.2
    · exact DsegC.2 c Good_C.2 d d_in_D c_le_d
end OrderExpander
