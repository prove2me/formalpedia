-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_simple_edge_bound_from_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:56:19.502604+00:00
-- url     : https://prove2.me/submissions/ae091c80-6f2c-46e2-9561-0de41cb2bb6b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_for_edge_bound_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_euler_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hcard, hHconn, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_for_edge_bound_v2 G hV hconn hG
  have hbound := WilliamsonShmoys.maximal_planar_drawing_edge_bound_euler_v2
    H hV hHconn hH hmax
  omega