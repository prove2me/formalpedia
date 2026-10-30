-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_some_edge_when_disconnected__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:15.029256+00:00
-- url     : https://prove2.me/submissions/90d5d0f5-4ab0-48ce-923b-50d13c9c27c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_disconnected_complement_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1
import Theorems.Thm_WilliamsonShmoys_insert_edge_along_avoiding_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hV : 0 < Fintype.card V) (hDisconnected : ¬ H.Connected) :
    ∃ G : SimpleGraph V, H ≤ G ∧
      ∃ u v : V, u ≠ v ∧ ¬ H.Adj u v ∧ G.Adj u v ∧ HasPlanarDrawingOn G := by
  obtain ⟨p, arc, hp⟩ := hDraw
  obtain ⟨u, v, γ, huv, hnot, hγ⟩ :=
    WilliamsonShmoys.planarDrawing_disconnected_complement_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1
      H p arc hp hV hDisconnected
  exact WilliamsonShmoys.insert_edge_along_avoiding_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1
    H p arc hp u v γ huv hnot hγ