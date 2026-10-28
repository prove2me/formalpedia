-- Prove2me | solution 1 for RendezvousKn.Sym.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:42.563979+00:00
-- url     : https://prove2.me/submissions/ce6fe07c-2cc0-4a91-acfa-6dd0a0c7960a

import Definitions.Def_RendezvousKn_Sym_Model

set_option autoImplicit false
open scoped BigOperators
open Finset RendezvousKn.Sym

theorem solution (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) :
    noRdvProb τA τB = probXZero (pairSet τA τB) := by
  have heq (π : Equiv.Perm (Fin n)) :
      (∀ i, π (τA i) ≠ τB i) ↔ matchCount (pairSet τA τB) π = 0 := by
    simp only [matchCount, card_eq_zero, filter_eq_empty_iff, pairSet, forall_mem_image,
      mem_univ, forall_true_left]
  unfold noRdvProb probXZero avgPerm
  congr 1
  apply sum_congr rfl
  intro π _
  simp only [heq π]

#print axioms solution
