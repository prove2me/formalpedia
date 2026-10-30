-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_with_maximal_planar_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:59:44.944357+00:00
-- url     : https://prove2.me/submissions/914301fd-f943-4304-8ed9-2c58cdb80ba1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal (L := L) hL
  have hCount :=
    WilliamsonShmoys.maximal_drawable_edge_count M hM hMax hV
  exact ⟨M, hLM, hM, hCount⟩