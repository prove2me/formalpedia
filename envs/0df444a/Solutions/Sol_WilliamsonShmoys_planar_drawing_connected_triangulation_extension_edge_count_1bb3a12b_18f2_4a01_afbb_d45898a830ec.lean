-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_triangulation_extension_edge_count_1bb3a12b_18f2_4a01_afbb_d45898a830ec
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:11:16.839338+00:00
-- url     : https://prove2.me/submissions/9bcd3206-816d-474c-a608-3a7524fb8e2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_connected_triangulation_extension_1bb3a12b

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hsub, hdrawH, hconnH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_exists G hdraw hconn
  exact ⟨H, hsub,
    WilliamsonShmoys.maximal_planar_edge_count_for_connected_triangulation_extension_1bb3a12b
      H hdrawH hconnH hmax hV⟩