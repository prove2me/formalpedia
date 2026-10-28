-- Prove2me | solution 1 for WilliamsonShmoys.planar_sparse_graph_has_drawable_strict_extension_dichotomy__p2m_5bb20037_ccd1_423f_b2f4_e98cccbfec38_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:24:41.131222+00:00
-- url     : https://prove2.me/submissions/371576d0-da94-4a7c-8a5d-9d3a24e208c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    (∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M) ∨
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
      L hL hCard
  by_cases hEq : M = L
  · right
    have hCount :=
      WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
        M hM hCard hMax
    simpa [hEq] using hCount
  · left
    exact ⟨M, hLM, hEq, hM⟩