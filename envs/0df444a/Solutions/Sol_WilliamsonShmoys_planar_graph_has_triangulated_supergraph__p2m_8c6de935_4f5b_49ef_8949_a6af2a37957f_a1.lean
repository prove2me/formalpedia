-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_8c6de935_4f5b_49ef_8949_a6af2a37957f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:52.86299+00:00
-- url     : https://prove2.me/submissions/575ae2cc-6bbe-42a5-bc4c-5b5cca1cbca7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hGL, hL, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_exists__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2 G hG
  exact ⟨L, hGL, hL,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_2facc1d9_8574_46e5_b6ec_a0ba2784b822_a2 L hL hMax hV⟩