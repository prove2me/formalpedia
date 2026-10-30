-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:59:23.653857+00:00
-- url     : https://prove2.me/submissions/d9940417-3e42-4a02-978c-5c20708f5730

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_for_edge_count_completion
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_edge_count_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_extension_for_edge_count_completion N hN
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_count_completion K hK hCard hMax
  refine ⟨K, hNK, hK, ?_⟩
  omega