-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_tight_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:37:59.299671+00:00
-- url     : https://prove2.me/submissions/b3427d1d-08a9-42a0-af7b-ea6bf9d0ab64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_tight_edge_count_ea3c3bca_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_tight_edge_count_ea3c3bca_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_tight_edge_count_ea3c3bca_maximal_extension
      K hK hcard
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.planar_supergraph_tight_edge_count_ea3c3bca_edge_count
      L hL hmax hcard⟩