-- Prove2me | solution 1 for UnboundedChain.f_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:19.206323+00:00
-- url     : https://prove2.me/submissions/11b792a7-940b-4f3b-87e7-ad8f07365e73

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α] [Inhabited α] [UnboundedChain α]
open UnboundedChain
namespace UnboundedChain
theorem _root_.solution : ∀ (C : Set α), IsChain (· ≤ ·) C → ∀ a ∈ C, a < f C := by
  intro C hC a ha
  have : f C = Classical.choose (strbd C hC) := by simp [*,f]
  rw [this]
  exact Classical.choose_spec (strbd C hC) a ha
end UnboundedChain
