-- Prove2me | solution 1 for SteinerNav.construction_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:27:49.224198+00:00
-- url     : https://prove2.me/submissions/51ae959b-ac94-486b-bce0-4c5c2d3c0dc3

import Mathlib
import Definitions.Def_SteinerNav_constructionEdges

open SteinerNav in
theorem solution {d : ℕ} (P Q S : Finset (Pt d)) :
    (constructionEdges P Q S).card ≤
        P.card * (S \ P).card + P.card * (Q.card + S.card) + (type3Edges P Q).card ∧
      ∀ m a : ℕ, Q.card = m → S.card ≤ m * a →
        P.card * (S \ P).card + P.card * (m + S.card) ≤ 2 * P.card * m * a + P.card * m ∧
          (1 ≤ a → 2 * P.card * m * a + P.card * m ≤ 3 * (P.card * m * a)) := by
  refine ⟨?_, ?_⟩
  · unfold constructionEdges
    refine le_trans (Finset.card_filter_le _ _) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
    rw [Finset.card_product, Finset.card_product]
    have h1 := Finset.card_union_le Q S
    have h2 : P.card * (Q ∪ S).card ≤ P.card * (Q.card + S.card) := Nat.mul_le_mul_left _ h1
    have h3 : (S \ P).card * P.card = P.card * (S \ P).card := Nat.mul_comm _ _
    omega
  · intro m a hm hS
    have hSP : (S \ P).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
    have h1 : P.card * (S \ P).card ≤ P.card * (m * a) := Nat.mul_le_mul_left _ (hSP.trans hS)
    have h2 : P.card * S.card ≤ P.card * (m * a) := Nat.mul_le_mul_left _ hS
    refine ⟨?_, fun ha => ?_⟩
    · have e1 : P.card * (m + S.card) = P.card * m + P.card * S.card := Nat.mul_add _ _ _
      have e2 : 2 * P.card * m * a = P.card * (m * a) + P.card * (m * a) := by ring
      omega
    · have h3 : P.card * m * 1 ≤ P.card * m * a := Nat.mul_le_mul_left _ ha
      have e3 : 3 * (P.card * m * a) = 2 * P.card * m * a + P.card * m * a := by ring
      omega
