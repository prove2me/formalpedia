-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_nonacyclic_face_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:37:30.10971+00:00
-- url     : https://prove2.me/submissions/dfac164c-cb99-4514-83dd-85c325e06e70

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_cyclic_edge_count_bound
import Theorems.Thm_WilliamsonShmoys_connected_nonacyclic_card_le_edge_ncard

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCyclic : ¬ G.IsAcyclic) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  have hEdgeBound :
      G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_cyclic_edge_count_bound
      G hConnected hDrawing hCyclic
  have hVerticesLEEdges :
      Fintype.card V ≤ G.edgeSet.ncard :=
    WilliamsonShmoys.connected_nonacyclic_card_le_edge_ncard
      G hConnected hCyclic
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_, ?_⟩
  · omega
  · omega