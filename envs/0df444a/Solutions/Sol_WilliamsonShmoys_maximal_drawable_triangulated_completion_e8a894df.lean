-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_triangulated_completion_e8a894df
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:50:30.53498+00:00
-- url     : https://prove2.me/submissions/f811bba7-081c-4296-b008-6f18edd95618

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_202d559d
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_202d559d

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_supergraph_202d559d K hK
  have hcount := WilliamsonShmoys.maximal_drawable_edge_count_202d559d L hV hL hmax
  exact ⟨L, hKL, hL, hcount⟩