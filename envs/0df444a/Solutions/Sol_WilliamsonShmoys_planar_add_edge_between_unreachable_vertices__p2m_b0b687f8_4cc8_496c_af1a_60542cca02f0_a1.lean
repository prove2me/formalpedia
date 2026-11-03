-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T09:13:38.40356+00:00
-- url     : https://prove2.me/submissions/c9e50743-dab7-478a-946d-6044215ce7ab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_add_edge_across_components__p2m_90599b14_5b71_48de_9bf9_85c7f1f2283c_a2
import Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hUV : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  have hGkeep := hG
  rcases hG with ⟨p, arc, hp, _⟩
  have huvne : u ≠ v := by
    intro huv
    apply hUV
    rw [huv]
    -- Rewriting by `huv` reduces the goal to reflexive reachability.
  by_cases hsmall : Fintype.card V < 3
  · refine ⟨⊤, le_top, ?_, ?_⟩
    · intro hEq
      have htop : (⊤ : SimpleGraph V).Adj u v := by
        simpa using huvne
      have hadj : G.Adj u v := hEq ▸ htop
      exact hUV (SimpleGraph.Adj.reachable hadj)
    · exact WilliamsonShmoys.small_card_complete_graph_planar_from_embedding__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1 p hp hsmall
  · have hnotconn : ¬ G.Connected := by
      intro hconn
      exact hUV (hconn u v)
    have hcard : 3 ≤ Fintype.card V := by omega
    obtain ⟨a, b, hab, hnab, K, hGK, hKab, hK⟩ :=
      WilliamsonShmoys.planarDrawingOn_add_edge_across_components__p2m_90599b14_5b71_48de_9bf9_85c7f1f2283c_a2
        G hGkeep hnotconn hcard
    refine ⟨K, hGK, ?_, hK⟩
    intro hEq
    apply hnab
    have hadj : G.Adj a b := hEq ▸ hKab
    exact hadj
