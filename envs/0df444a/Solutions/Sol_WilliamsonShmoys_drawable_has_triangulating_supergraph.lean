-- Prove2me | solution 1 for WilliamsonShmoys.drawable_has_triangulating_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:48:59.481777+00:00
-- url     : https://prove2.me/submissions/def4fda6-df16-4d07-81c4-9cc13cabfe14

import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ H : SimpleGraph V, U ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨H, hUH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_extension U hU
  exact ⟨H, hUH, hH,
    WilliamsonShmoys.maximal_drawable_edge_lower_bound H hV hH hmax⟩