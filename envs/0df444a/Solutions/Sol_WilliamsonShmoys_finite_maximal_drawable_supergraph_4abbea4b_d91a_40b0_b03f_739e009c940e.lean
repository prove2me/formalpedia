-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_drawable_supergraph_4abbea4b_d91a_40b0_b03f_739e009c940e
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:28:08.981382+00:00
-- url     : https://prove2.me/submissions/ed8e422b-fa21-4507-aa30-3776cf20b6c6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_of_subgraph_closed
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_subgraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ P : SimpleGraph V, M ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q →
        WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by
  exact WilliamsonShmoys.finite_maximal_supergraph_of_subgraph_closed
    WilliamsonShmoys.HasPlanarDrawingOn
    (by
      intro G H hGH hH
      exact WilliamsonShmoys.planar_drawingOn_subgraph hGH hH)
    M hM