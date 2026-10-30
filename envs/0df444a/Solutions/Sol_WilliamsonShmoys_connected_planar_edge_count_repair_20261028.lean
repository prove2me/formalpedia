-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_repair_20261028
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T14:02:12.740452+00:00
-- url     : https://prove2.me/submissions/9a05f41e-db50-462f-a6a0-e4cf4865e1fa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_repair_20261028_triangulation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConnected : H.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDraw, hKCard⟩ :=
    WilliamsonShmoys.connected_planar_edge_count_repair_20261028_triangulation
      H hConnected hDraw hCard
  have hEdges : H.edgeSet ⊆ K.edgeSet := by
    exact SimpleGraph.edgeSet_mono hHK
  have hNcard : H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_mono hEdges
  rw [hKCard] at hNcard
  omega
