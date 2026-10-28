-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_repair_20261028_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:26:49.142591+00:00
-- url     : https://prove2.me/submissions/a75b2163-a5a9-458d-9aab-3a981eb6f3bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_repair_20261028_maximal_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_repair_20261028_maximal_planar_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConnected : H.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKDraw, hKMax⟩ :=
    WilliamsonShmoys.connected_planar_edge_count_repair_20261028_maximal_extension
      H hConnected hDraw hCard
  exact ⟨K, hHK, hKDraw,
    WilliamsonShmoys.connected_planar_edge_count_repair_20261028_maximal_planar_edge_count
      K hKDraw hKMax hCard⟩