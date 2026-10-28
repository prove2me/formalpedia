-- Prove2me | solution 1 for WilliamsonShmoys.three_face_sides_for_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:06:59.918153+00:00
-- url     : https://prove2.me/submissions/c00bd50b-4b30-483a-a997-7a7f04f700e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_ea237986_dde8_45aa_8717_82b33fafcc6c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V)
    (f : Nat)
    (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f <= 2 * G.edgeSet.ncard := by
  have hBound :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_ea237986_dde8_45aa_8717_82b33fafcc6c
      G hG hConn hCard
  omega
