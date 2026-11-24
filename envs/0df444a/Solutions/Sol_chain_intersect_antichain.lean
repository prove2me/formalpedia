-- Prove2me | solution 1 for chain_intersect_antichain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:08:42.664265+00:00
-- url     : https://prove2.me/submissions/2cde73b3-25ae-4a5a-96d2-01f19118bd13

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.WellFoundedSet
import Definitions.Def_AharoniKorman_ForMathlib_Misc

set_option autoImplicit true

theorem _root_.solution {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : IsChain (· ≤ ·) s) (ht : IsAntichain (· ≤ ·) t) :
    (s ∩ t).Subsingleton := by
  simp only [Set.Subsingleton, Set.mem_inter_iff, and_imp]
  intro x hxs hxt y hys hyt
  by_contra! hne
  cases hs.total hxs hys
  case inl h => exact ht hxt hyt hne h
  case inr h => exact ht hyt hxt hne.symm h
