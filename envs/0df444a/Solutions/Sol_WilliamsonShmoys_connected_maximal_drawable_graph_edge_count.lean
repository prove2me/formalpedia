-- Prove2me | solution 1 for WilliamsonShmoys.connected_maximal_drawable_graph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:25:24.246987+00:00
-- url     : https://prove2.me/submissions/642a09cf-e8c3-4f4a-aa73-5ed8c5dfe63d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_for_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Q.Connected)
    (hmax : ∀ M : SimpleGraph V,
      Q ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M ≤ Q) :
    3 * Fintype.card V - 6 = Q.edgeSet.ncard := by
  obtain ⟨M, hQM, hMDrawing, hMCount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph_for_edge_count
      Q hQ hV hconn
  have hMQ : M ≤ Q := hmax M hQM hMDrawing
  have hEq : M = Q := le_antisymm hMQ hQM
  rw [hEq] at hMCount
  exact hMCount