-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph_from_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:26:39.468019+00:00
-- url     : https://prove2.me/submissions/a7eb7ea0-ecff-4ed0-8a48-d46e34e5f82a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_on_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_on_vertices

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maximal_on_vertices H hV hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_on_vertices K hV hK hmax⟩