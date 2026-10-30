-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension_via_maximality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:32:22.742063+00:00
-- url     : https://prove2.me/submissions/451efb14-083c-47e9-bee9-9f51af112274

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal_for_extension_561cc06e
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_inclusion_maximal_drawing_561cc06e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun L : SimpleGraph V =>
      And (Set.Subset K.edgeSet L.edgeSet)
        (And (WilliamsonShmoys.HasPlanarDrawingOn L)
          (L.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_maximal_for_extension_561cc06e K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.planar_edge_count_of_inclusion_maximal_drawing_561cc06e
      L hL hV hmax⟩