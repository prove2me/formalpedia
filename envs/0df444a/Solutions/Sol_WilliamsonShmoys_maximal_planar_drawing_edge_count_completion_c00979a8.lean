-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_completion_c00979a8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:46:07.482468+00:00
-- url     : https://prove2.me/submissions/f820cfdb-5c4c-4d34-bba8-f1fc658203ae

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists_repair_57fa5dbe_60fc_4f14_8396_90559c67382e
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_repair_57fa5dbe_60fc_4f14_8396_90559c67382e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists_repair_57fa5dbe_60fc_4f14_8396_90559c67382e K hV hK
  have hbound := WilliamsonShmoys.maximal_planar_edge_bound_repair_57fa5dbe_60fc_4f14_8396_90559c67382e L hV hL hmax
  exact ⟨L, hKL, hL, hbound⟩