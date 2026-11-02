-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:47:40.537829+00:00
-- url     : https://prove2.me/submissions/d4c13fc7-65bd-4d84-9eaf-33d26c442b81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_mono__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hconn : G.Connected) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨H, hGH, hHplanar, hHeq⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
      G hV hG hconn
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hmono :=
    WilliamsonShmoys.edgeFinset_mono__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
      G H hGH
  omega