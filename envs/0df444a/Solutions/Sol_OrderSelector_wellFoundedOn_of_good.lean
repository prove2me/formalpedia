-- Prove2me | solution 1 for OrderSelector.wellFoundedOn_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:47:33.958613+00:00
-- url     : https://prove2.me/submissions/b7ae4704-c14b-45d5-9869-0ee70339a0d6

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_OrderSelector_wellOrdered_of_good

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α] [OrderSelector α]
open OrderExpander
open OrderSelector
namespace OrderSelector
theorem _root_.solution {C : Set α} (hC : Good C) : C.WellFoundedOn (· < ·) := by
  rw [wellFoundedOn_iff, WellFounded.wellFounded_iff_has_min]
  intro t ⟨m₀, hm₀⟩
  by_cases hm₀C : m₀ ∈ C
  · obtain ⟨m, hm, hmin⟩ :=
      wellOrdered_of_good hC {x : α | x ∈ t ∧ x ∈ C} (fun x hx => hx.2) ⟨m₀, hm₀, hm₀C⟩
    exact ⟨m, hm.1, fun x hx h => lt_irrefl m (lt_of_le_of_lt (hmin x ⟨hx, h.2.1⟩) h.1)⟩
  · exact ⟨m₀, hm₀, fun x _ h => absurd h.2.2 hm₀C⟩
end OrderSelector
