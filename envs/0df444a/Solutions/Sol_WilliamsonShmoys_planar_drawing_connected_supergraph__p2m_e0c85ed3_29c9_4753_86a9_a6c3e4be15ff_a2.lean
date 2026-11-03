-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:54:50.99395+00:00
-- url     : https://prove2.me/submissions/32dacd8f-cc3a-4cca-bbf9-c15d468df9df

import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
import Theorems.Thm_WilliamsonShmoys_finite_graph_extension_connected__p2m_a6ee2644_08f0_4c4d_a139_48d0925fab45_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 0 < Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp hcard
  apply WilliamsonShmoys.finite_graph_extension_connected__p2m_a6ee2644_08f0_4c4d_a139_48d0925fab45_a1
    WilliamsonShmoys.HasPlanarDrawingOn H hdraw
  intro G hG hnot
  have huv : ∃ u v : V, ¬ G.Reachable u v := by
    by_contra h
    push_neg at h
    apply hnot
    exact ⟨h⟩
  obtain ⟨u, v, huv⟩ := huv
  obtain ⟨K, hGK, hne, hK⟩ :=
    WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1 G hG u v huv
  exact ⟨K, hGK, Ne.symm hne, hK⟩
