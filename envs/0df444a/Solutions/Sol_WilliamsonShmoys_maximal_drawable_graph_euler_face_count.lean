-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_euler_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:30:24.132196+00:00
-- url     : https://prove2.me/submissions/b31f4817-61e9-4cae-9f91-336f89387bde
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
import Theorems.Thm_WilliamsonShmoys_connected_graph_edge_count_lower_bound__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by
  have hConnected : L.Connected :=
    WilliamsonShmoys.maximal_drawable_graph_connected__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
      L hL hMax hCard
  have hEdges : Fintype.card V ≤ L.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_graph_edge_count_lower_bound__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
      L hConnected
  refine ⟨L.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega