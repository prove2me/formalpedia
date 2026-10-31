-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound__p2m_c23ffc9b_3ccd_4354_ad9d_982ada7aecad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:27:27.466406+00:00
-- url     : https://prove2.me/submissions/5ddece91-7416-4cb0-8e41-257d777e671b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_edge_count__p2m_7aa08c57_80e4_4bfa_956e_5ec8913e85a2_a4
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hcard_le, hcard_eq⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_supergraph_edge_count__p2m_7aa08c57_80e4_4bfa_956e_5ec8913e85a2_a4 H hH hV
  exact hcard_le.trans (le_of_eq hcard_eq)