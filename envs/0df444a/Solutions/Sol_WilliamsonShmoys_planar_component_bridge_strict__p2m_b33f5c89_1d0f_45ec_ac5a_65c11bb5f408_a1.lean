-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_bridge_strict__p2m_b33f5c89_1d0f_45ec_ac5a_65c11bb5f408_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:14:16.225275+00:00
-- url     : https://prove2.me/submissions/4bba080e-05a9-4eac-ae3c-d3c8610173c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_component_bridge_extension__p2m_654d6b40_351a_4feb_9abd_94332c593474_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) (hNotConnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard < H.edgeSet.ncard ∧
      (∀ u v, G.Reachable u v → H.Reachable u v) ∧
      (∃ u v, ¬ G.Reachable u v ∧ H.Reachable u v) := by
  obtain ⟨H, hGH, hHDraw, hEdges, u, v, hUnreachable, hAdjacent⟩ :=
    planar_component_bridge_extension__p2m_654d6b40_351a_4feb_9abd_94332c593474_a1
      G hDraw hCard hNotConnected
  refine ⟨H, hGH, hHDraw, hEdges, ?_, ?_⟩
  · intro x y hReach
    exact hReach.mono hGH
  · exact ⟨u, v, hUnreachable, hAdjacent.reachable⟩