-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_completion_edge_count__p2m_326c8e6c_2fee_4ab9_b71e_76b7c3f2eeb5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:23.514581+00:00
-- url     : https://prove2.me/submissions/b871d177-7c1d-473a-9893-0e299a7a5e81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hGM, hMDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2 G hDraw
  refine ⟨M, hGM, hMDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2 M hMDraw hV hMax