-- Prove2me | solution 1 for WilliamsonShmoys_planar_small_card_completion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:00:43.747034+00:00
-- url     : https://prove2.me/submissions/9622e3ba-66cf-4697-9f9e-43007e4080ff

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
import Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_edge_count__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsmall : Fintype.card V < 3) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H ≤ K ∧
      K.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  rcases hH with ⟨p, arc, hp, _⟩
  let K : SimpleGraph V := ⊤
  letI : DecidableRel K.Adj := Classical.decRel _
  refine ⟨K, inferInstance, ?_, ?_, ?_⟩
  · simpa [K] using (WilliamsonShmoys.small_card_complete_graph_planar_from_embedding__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1 (V := V) p hp hsmall)
  · exact le_top
  · simpa [K] using (WilliamsonShmoys.small_card_complete_graph_edge_count__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1 (V := V) hsmall)