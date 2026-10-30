-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_augmentation__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:09.030993+00:00
-- url     : https://prove2.me/submissions/57e9d544-ebd8-401d-9752-4cf39c029460
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_reachability_augmentation__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1
import Theorems.Thm_WilliamsonShmoys_planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hGH, hPlanar, hConnected, hCardMono⟩ :=
    WilliamsonShmoys.finite_reachability_augmentation__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1
      (P := WilliamsonShmoys.HasPlanarDrawingOn) G hDraw
      (by
        intro K hK hNotConnected
        exact WilliamsonShmoys.planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1
          K hK hNotConnected)
  exact ⟨H, hGH, hConnected, hPlanar, hCardMono⟩