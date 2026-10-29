-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:14:03.201032+00:00
-- url     : https://prove2.me/submissions/986ca8e1-cc68-4309-9ce1-c636bdb65948
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_edge_bound__p2m_1aad81a2_ffc1_486e_a5cd_7c6b31189477_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, _hGH, _hdrawH, _hconnH, hmono, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_extension_edge_bound__p2m_1aad81a2_ffc1_486e_a5cd_7c6b31189477_a2
      G hconn hdraw hCard
  omega