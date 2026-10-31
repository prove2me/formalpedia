-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_8d118255_640d_459b_9d55_e13b141f8172_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:19.719318+00:00
-- url     : https://prove2.me/submissions/e6c5aa69-9df7-414b-9c0e-51370a1ad347

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨K, hLK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
      L hL
  exact ⟨K, hLK, hK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
      K hK hmax hV⟩