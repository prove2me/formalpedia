-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_maximal_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:12:21.661418+00:00
-- url     : https://prove2.me/submissions/701125ba-8c84-424a-9781-c41d84473c06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_by_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hmax, hcardLower⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count K hK
  have hcount := WilliamsonShmoys.maximal_planar_edge_count_by_triangulation
    H hV hH hmax
  exact ⟨H, hH, hcardLower, hcount⟩