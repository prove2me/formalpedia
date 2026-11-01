-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:21:05.930117+00:00
-- url     : https://prove2.me/submissions/f7a48389-eeaa-474b-ab3c-3463923b7a7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_from_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.connected_planar_supergraph_from_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
    G hplanar
    (fun K hGK hKdraw hKdisconnected =>
      WilliamsonShmoys.planar_drawing_edge_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
        K hKdraw hKdisconnected)