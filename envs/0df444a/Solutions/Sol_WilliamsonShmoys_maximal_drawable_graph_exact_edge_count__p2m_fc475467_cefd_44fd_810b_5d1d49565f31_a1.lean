-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_exact_edge_count__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:56:15.52586+00:00
-- url     : https://prove2.me/submissions/81909281-7de6-4a77-8f97-45e28c75d73a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_cc47608f_2603_41cf_ab7f_de8b10963069_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨T, hLT, hT, hcount⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_cc47608f_2603_41cf_ab7f_de8b10963069_a1 L hV hL
  have hEq := hmax T hLT hT
  rw [← hEq]
  exact hcount