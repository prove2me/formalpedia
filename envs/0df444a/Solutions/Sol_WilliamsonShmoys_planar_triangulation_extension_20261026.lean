-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:05:49.288521+00:00
-- url     : https://prove2.me/submissions/a44e6a6a-6410-487b-8c9f-9f104e944166
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_supergraph_20261026
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_edge_count_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, J ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hJL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_maximal_supergraph_20261026 J hJ
  refine ⟨L, hJL, hL, ?_⟩
  exact WilliamsonShmoys.planar_triangulation_extension_maximal_edge_count_20261026
    L hL hmax hV