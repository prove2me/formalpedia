-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:58.483155+00:00
-- url     : https://prove2.me/submissions/1c41df37-0d6d-440e-a8c2-62fea8258d4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_component_bridge_strict__p2m_b33f5c89_1d0f_45ec_ac5a_65c11bb5f408_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) (hNotConnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v, G.Reachable u v → H.Reachable u v) ∧
      (∃ u v, ¬ G.Reachable u v ∧ H.Reachable u v) := by
  obtain ⟨H, hGH, hDrawH, hEdges, hReach, u, v, hu, hv⟩ :=
    WilliamsonShmoys.planar_component_bridge_strict__p2m_b33f5c89_1d0f_45ec_ac5a_65c11bb5f408_a1
      G hDraw hCard hNotConnected
  exact ⟨H, hGH, hDrawH, le_of_lt hEdges, hReach, ⟨u, v, hu, hv⟩⟩