-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.natDist_card_le_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/9af46901-8041-4866-8977-b9018ba0f0fb

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {α : Type*} [DecidableEq α]
    (A B : Finset α) :
    Nat.dist A.card B.card ≤ (A \ B).card + (B \ A).card := by
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  have hinter : (A ∩ B).card = (B ∩ A).card := by
    rw [Finset.inter_comm]
  by_cases h : A.card ≤ B.card
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_not_ge h)]
    omega
end SoficGroups.KunThomFiberCoarea
