-- Prove2me | solution 1 for bourbaki_witt_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:48:37.251421+00:00
-- url     : https://prove2.me/submissions/1a218c13-7390-455a-b718-eb005b174f6e

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_ChainBounding_chain_bounding

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open ChainBounding
theorem _root_.solution [CompletePartialOrder α] (g : α → α) (hg : ∀x, x ≤ g x) :
    ∃ x, g x = x := by
  by_contra noFix ; push Not at noFix
  let inst : OrderSelector α := ⟨(g $ sSup ·)⟩
  have : ChainBounding α := by
    constructor
    intro C chain a ha
    calc
      a ≤ sSup C := DirectedOn.le_sSup (IsChain.directedOn chain) ha
      _ < OrderSelector.f C := lt_of_le_of_ne' (hg (sSup C)) (noFix (sSup C))
  exact chain_bounding (α := α)
