-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_completion_maximal_extension_for_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:48:22.85075+00:00
-- url     : https://prove2.me/submissions/c01054df-4615-4990-8331-27dcbbe22616

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_predicate_has_maximal_extension

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  exact WilliamsonShmoys.finite_graph_predicate_has_maximal_extension
    WilliamsonShmoys.HasPlanarDrawingOn N hN