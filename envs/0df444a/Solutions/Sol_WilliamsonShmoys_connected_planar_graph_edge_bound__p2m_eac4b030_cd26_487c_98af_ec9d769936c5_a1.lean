-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:06.722823+00:00
-- url     : https://prove2.me/submissions/f3c44aee-98df-496f-8c13-b467e3f54360
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_euler_face_count__p2m_9357b4e9_1465_44fb_ab01_49fb91da15d0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceIncidence⟩ :=
    WilliamsonShmoys.connected_planar_graph_euler_face_count__p2m_9357b4e9_1465_44fb_ab01_49fb91da15d0_a1
      H hHconn hHdraw hV
  omega