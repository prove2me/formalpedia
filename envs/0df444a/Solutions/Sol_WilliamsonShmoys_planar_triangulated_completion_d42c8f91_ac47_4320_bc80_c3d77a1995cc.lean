-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:51:56.612301+00:00
-- url     : https://prove2.me/submissions/552484d9-255d-44cf-a88a-2b370d424792
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
      H hV hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_graph_edge_count_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
      K hV hK hmax⟩