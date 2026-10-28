-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_drawing_has_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:05:26.069567+00:00
-- url     : https://prove2.me/submissions/a8466d03-eb1a-4ced-a04a-cf5e62c71507
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_drawable_graph_has_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.finite_drawable_graph_has_maximal_supergraph N hV hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count
      K hV hK hMax⟩