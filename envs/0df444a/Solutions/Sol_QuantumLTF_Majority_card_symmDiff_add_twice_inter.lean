-- Prove2me | solution 1 for QuantumLTF.Majority.card_symmDiff_add_twice_inter
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-16T22:59:04.490743+00:00
-- url     : https://prove2.me/submissions/6d2524f2-0f97-44c5-9255-b8f85df3d605

import Mathlib

open scoped symmDiff

theorem solution : ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α),
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  intro α _ _ A B
  rw [Finset.symmDiff_def]
  have hd : Disjoint (A \ B) (B \ A) := by
    refine Finset.disjoint_left.2 ?_
    intro a ha hb
    simp only [Finset.mem_sdiff] at ha hb
    exact ha.2 hb.1
  rw [Finset.card_union_of_disjoint hd]
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at hB
  omega

