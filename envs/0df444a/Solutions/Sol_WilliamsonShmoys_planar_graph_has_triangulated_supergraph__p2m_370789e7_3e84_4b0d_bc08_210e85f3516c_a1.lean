-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_370789e7_3e84_4b0d_bc08_210e85f3516c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:06.926989+00:00
-- url     : https://prove2.me/submissions/8e7d661a-d128-4b0e-9d11-7e51a34857af

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_supergraph__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_graph_has_maximal_supergraph__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
      L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
      M hM hV hMax⟩