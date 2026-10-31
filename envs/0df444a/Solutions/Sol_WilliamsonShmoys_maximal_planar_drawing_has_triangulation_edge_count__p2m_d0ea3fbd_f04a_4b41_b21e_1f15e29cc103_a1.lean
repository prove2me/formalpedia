-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:07:32.454961+00:00
-- url     : https://prove2.me/submissions/ac026933-dd2b-47ff-bbc7-5981333722f4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1
import Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation_below_triangulation_count__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1

set_option autoImplicit false

/-- Euler's formula and triangular faces give the edge count for an inclusion-maximal planar graph. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hMax : forall K : SimpleGraph V, G <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1
    G hDraw hV
  have hLower : 3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
    by_contra h
    have hlt : G.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
    obtain ⟨K, hGK, hKG, hKDraw⟩ :=
      WilliamsonShmoys.planar_graph_augmentation_below_triangulation_count__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1
        G hDraw hV hlt
    exact hKG (hMax K hGK hKDraw)
  omega