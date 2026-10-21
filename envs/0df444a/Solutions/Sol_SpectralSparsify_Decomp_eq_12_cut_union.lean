-- Prove2me | solution 1 for SpectralSparsify.Decomp.eq_12_cut_union
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:25:16.798621+00:00
-- url     : https://prove2.me/submissions/3715f0c5-e56e-4ebb-ae21-174927aae4a8

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_cutEdges

set_option autoImplicit false
open SpectralSparsify.Decomp

theorem solution {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (B S R : Finset V) (hSB : S ⊆ B) (hRB : R ⊆ B \ S) :
    cutEdges G (R ∪ S) (B \ (R ∪ S)) ≤ cutEdges G S (B \ S) + cutEdges G R ((B \ S) \ R) := by
  unfold cutEdges
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_sdiff] at hp ⊢
  obtain ⟨⟨hu, hv⟩, hadj⟩ := hp
  by_cases hs : p.1 ∈ S
  · left
    refine ⟨⟨hs, ?_⟩, hadj⟩
    tauto
  · right
    have hr : p.1 ∈ R := by
      rcases hu with h | h
      · exact h
      · exact absurd h hs
    refine ⟨⟨hr, ?_⟩, hadj⟩
    tauto
