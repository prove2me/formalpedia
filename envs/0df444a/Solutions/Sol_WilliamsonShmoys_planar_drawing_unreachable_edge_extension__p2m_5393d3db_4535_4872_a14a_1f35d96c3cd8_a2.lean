-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_unreachable_edge_extension__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:53.191561+00:00
-- url     : https://prove2.me/submissions/1f24057d-9574-4cdc-ae04-3d66666d7e1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_connected_supergraph__p2m_7b51bdb4_4dea_43b6_9d51_b05a3b3a7c9a_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (u v : V)
    (huv : u ≠ v)
    (hUnreachable : ¬ M.Reachable u v) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N ≠ M ∧ HasPlanarDrawingOn N := by
  obtain ⟨N, hMN, hConnected, hPlanar⟩ :=
    WilliamsonShmoys.planar_graph_connected_supergraph__p2m_7b51bdb4_4dea_43b6_9d51_b05a3b3a7c9a_a2
      M hM ⟨u⟩
  refine ⟨N, hMN, ?_, hPlanar⟩
  intro hEq
  apply hUnreachable
  simpa [hEq] using hConnected u v