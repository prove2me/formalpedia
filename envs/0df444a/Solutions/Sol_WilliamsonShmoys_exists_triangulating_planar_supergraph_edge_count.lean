-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulating_planar_supergraph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:54:51.417833+00:00
-- url     : https://prove2.me/submissions/cc9e2f36-610f-432c-b09a-78fd46889d7b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices_71a098b3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_71a098b3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_71a098b3 J hJ
  exact ⟨K, hJK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_71a098b3 K hK hmax hcard⟩
