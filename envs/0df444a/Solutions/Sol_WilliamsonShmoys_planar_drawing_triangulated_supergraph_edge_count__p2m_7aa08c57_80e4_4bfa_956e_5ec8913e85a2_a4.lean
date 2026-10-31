-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_supergraph_edge_count__p2m_7aa08c57_80e4_4bfa_956e_5ec8913e85a2_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:31:17.688881+00:00
-- url     : https://prove2.me/submissions/21313c86-1c06-49b1-aebb-4df006064f68

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hEdges, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1 H hH
  have hcount := WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1 K hK hmax hV
  exact ⟨K, hHK, hK, hEdges, hcount⟩