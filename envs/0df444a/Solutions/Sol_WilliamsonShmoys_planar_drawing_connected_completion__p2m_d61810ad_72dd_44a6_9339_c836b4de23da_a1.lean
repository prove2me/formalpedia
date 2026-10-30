-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_completion__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:35.611548+00:00
-- url     : https://prove2.me/submissions/37e61d20-c9bd-4fe6-908e-91b8e96c077b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_connected_completion__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLplanar : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  by_cases hconn : L.Connected
  · exact ⟨L, le_rfl, hLplanar, hconn, le_rfl⟩
  · obtain ⟨H, hLH, hHplanar, hHconn, hEdges⟩ :=
      WilliamsonShmoys.planar_drawing_disconnected_connected_completion__p2m_9c676d6c_6d6d_407a_ad73_9f103d372166_a5
        L hLplanar hV hconn
    exact ⟨H, hLH, hHplanar, hHconn, hEdges.le⟩