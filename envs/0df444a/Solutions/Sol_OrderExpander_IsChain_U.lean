-- Prove2me | solution 1 for OrderExpander.IsChain_U
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:47:04.894686+00:00
-- url     : https://prove2.me/submissions/105f3ba4-de98-44bd-b211-d7b17621c27b

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
theorem _root_.solution : IsChain (· ≤ ·) (U  (α := α)) := by
  intro c c_in_U d d_in_U c_ne_d
  obtain ⟨C, hC⟩ := c_in_U
  obtain ⟨D, hD⟩ := d_in_U
  rcases comparability C D hC.1 hD.1 with CsegD | DsegC
  · exact hD.1.1 (CsegD.1 hC.2) hD.2 c_ne_d
  · exact hC.1.1 hC.2 (DsegC.1 hD.2) c_ne_d
end OrderExpander
