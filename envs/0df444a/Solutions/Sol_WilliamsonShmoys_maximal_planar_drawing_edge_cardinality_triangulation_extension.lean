-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_cardinality_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:50:56.582331+00:00
-- url     : https://prove2.me/submissions/65e109ed-56c5-4654-a58f-fa53ee3c4f6a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_drawing_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hKmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_drawing_supergraph H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count K hV hK hKmax⟩