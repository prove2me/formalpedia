-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph_same_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:08:58.910389+00:00
-- url     : https://prove2.me/submissions/f7a95f92-77fa-41f5-9861-1e4d666d7114
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hST, hT, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices S hS
  exact ⟨T, hST, hT,
    WilliamsonShmoys.maximal_drawable_graph_edge_count T hV hT hMax⟩