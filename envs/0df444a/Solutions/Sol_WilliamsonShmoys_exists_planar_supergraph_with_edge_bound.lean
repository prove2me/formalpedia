-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:37:24.868985+00:00
-- url     : https://prove2.me/submissions/c6aac36d-6f7e-4de5-8c64-58ca2ba73db1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_cda78d6a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_edge_bound_cda78d6a

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLDrawing, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_cda78d6a K hDrawing
  exact ⟨L, hKL, hLDrawing,
    WilliamsonShmoys.maximal_planar_graph_has_edge_bound_cda78d6a
      L hLDrawing hCard hMax⟩