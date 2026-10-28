-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_formula_bf226c5d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:26:47.812447+00:00
-- url     : https://prove2.me/submissions/8769f3c6-aa56-4f5a-b9b1-2f2d650d9642

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hEdgeNat := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hConnected
  have hEdge : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    simpa using hEdgeNat
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega