-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_of_edge_insertions
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:13:16.54903+00:00
-- url     : https://prove2.me/submissions/1c8f097b-7101-4382-be71-82af445d8ffb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_extension_ascent

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hstep : ∀ (L : SimpleGraph V), K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → ¬ L.Connected →
      ∃ M : SimpleGraph V, L ≤ M ∧
        WilliamsonShmoys.HasPlanarDrawingOn M ∧
        L.edgeSet.ncard < M.edgeSet.ncard) :
    ∃ K' : SimpleGraph V, K ≤ K' ∧ K'.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K.edgeSet.ncard ≤ K'.edgeSet.ncard := by
  obtain ⟨K', hKK', hconn, hdraw', hcard⟩ :=
    WilliamsonShmoys.finite_graph_extension_ascent
      K WilliamsonShmoys.HasPlanarDrawingOn hdraw hstep
  exact ⟨K', hKK', hconn, hdraw', hcard⟩