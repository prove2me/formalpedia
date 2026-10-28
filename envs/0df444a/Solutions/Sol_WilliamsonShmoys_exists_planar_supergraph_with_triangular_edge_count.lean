-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_triangular_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:46:45.013008+00:00
-- url     : https://prove2.me/submissions/95600325-0777-4b84-9bc7-a5ee3c886114
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangular_edge_count_maximal_e20a9b21
import Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_planar_supergraph_e20a9b21

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hL, hKL, hMax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_triangular_edge_count_maximal_e20a9b21
      K hDrawing
  exact ⟨L, hL, hKL,
    WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_supergraph_e20a9b21
      L hL hCard hMax⟩