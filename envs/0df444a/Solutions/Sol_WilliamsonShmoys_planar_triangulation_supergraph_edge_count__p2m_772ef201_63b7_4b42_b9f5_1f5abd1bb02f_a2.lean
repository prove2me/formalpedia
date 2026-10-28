-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_772ef201_63b7_4b42_b9f5_1f5abd1bb02f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:47:33.110593+00:00
-- url     : https://prove2.me/submissions/763dae9a-b5bd-4472-b0ec-af001f57a08c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2 G hG
  refine ⟨H, hGH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2 H hH hmax hV