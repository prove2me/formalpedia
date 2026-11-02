-- Prove2me | solution 1 for WilliamsonShmoys.small_card_complete_graph_planar_from_embedding__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:10.220088+00:00
-- url     : https://prove2.me/submissions/49e5b450-7b01-4dc1-bbb6-65ae75dad188

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding_vertices_exhausted__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
import Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding_segment_geometry__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
import Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding_edge_pair_unique__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (p : V -> Real × Real) (hp : Function.Injective p)
    (hsmall : Fintype.card V < 3) :
    HasPlanarDrawingOn (⊤ : SimpleGraph V) := by
  let arc : V -> V -> Real -> Real × Real :=
    fun u v t => (1 - t) • p u + t • p v
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    have hvertices :=
      WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_vertices_exhausted__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
        (V := V) hsmall u v (ne_of_lt huv)
    rcases
      WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_segment_geometry__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
        (V := V) p hp u v huv hvertices with
      ⟨hcont, hinj, hzero, hone, havoid⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [arc] using hcont
    · simpa [arc] using hinj
    · simpa [arc] using hzero
    · simpa [arc] using hone
    · intro t ht w
      exact havoid t ht w
  · intro u v x y huv hxy hadj1 hadj2 hne t ht s hs heq
    exact False.elim
      (WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_edge_pair_unique__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
        (V := V) hsmall u v x y huv hxy hne)