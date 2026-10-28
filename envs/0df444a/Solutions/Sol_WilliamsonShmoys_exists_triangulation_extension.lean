-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:44:33.436605+00:00
-- url     : https://prove2.me/submissions/0e76be65-7ba2-407c-90c6-d32764fcd573
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_triangulation
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_for_triangulation K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_drawable_graph_has_triangulation_count L hV hL hmax⟩