-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:05:46.301588+00:00
-- url     : https://prove2.me/submissions/ac396e6c-347a-4ed1-8e79-c80448067215

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_651e6155_repair2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_651e6155_repair2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊆ M.edgeSet ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hM, hLM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_651e6155_repair2 L hDrawing
  exact ⟨M, hM, hLM,
    WilliamsonShmoys.maximal_planar_supergraph_edge_count_651e6155_repair2 M hM hmax hCard⟩