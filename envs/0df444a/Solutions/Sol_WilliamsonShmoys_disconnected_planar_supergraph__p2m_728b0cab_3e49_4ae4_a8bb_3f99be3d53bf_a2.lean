-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_supergraph__p2m_728b0cab_3e49_4ae4_a8bb_3f99be3d53bf_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:10.910756+00:00
-- url     : https://prove2.me/submissions/4a21cdc4-d162-4dc4-89b1-b5e552b2acb4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_add_some_edge_when_disconnected__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hV : 0 < Fintype.card V) (hDisconnected : ¬ H.Connected) :
    ∃ G : SimpleGraph V, H ≤ G ∧ G ≠ H ∧ HasPlanarDrawingOn G := by
  obtain ⟨G, hsub, u, v, huv, hnotAdj, hnewAdj, hGDraw⟩ :=
    WilliamsonShmoys.planar_add_some_edge_when_disconnected__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a2
      H hDraw hV hDisconnected
  refine ⟨G, hsub, ?_, hGDraw⟩
  intro heq
  subst G
  exact hnotAdj hnewAdj