-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_edge_bound__p2m_a3d46af7_d8d1_44e5_ae3d_980c06c923f9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:55:02.041181+00:00
-- url     : https://prove2.me/submissions/ca720545-b38b-4790-b574-f2691f258b1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_maximal_drawable__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set V) [Fintype S]
    (G : SimpleGraph S)
    (hDraw : HasPlanarDrawingOn G)
    (hcard : 3 ≤ S.ncard) :
    ∃ N : SimpleGraph S, G ≤ N ∧ HasPlanarDrawingOn N ∧
      3 * S.ncard ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨N, hGN, hNdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
      (S := S) G hDraw
  refine ⟨N, hGN, hNdraw, ?_⟩
  exact WilliamsonShmoys.edge_bound_of_maximal_drawable__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
    (S := S) (N := N) hNdraw hcard hmax
