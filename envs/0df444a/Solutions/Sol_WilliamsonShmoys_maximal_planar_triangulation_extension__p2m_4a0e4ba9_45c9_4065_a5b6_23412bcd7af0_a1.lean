-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_4a0e4ba9_45c9_4065_a5b6_23412bcd7af0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:22:03.815207+00:00
-- url     : https://prove2.me/submissions/25f8b910-fde4-46a2-9c61-150136c0eb66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_inclusion_maximal__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
        3 * Fintype.card V = L.edgeFinset.card + 6) := by
  classical
  obtain ⟨L, hKL, hL, hMax⟩ := WilliamsonShmoys.planar_extension_to_inclusion_maximal__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1 K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1 L hV hL hMax