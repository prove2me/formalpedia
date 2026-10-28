-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_completion_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:14:22.071255+00:00
-- url     : https://prove2.me/submissions/0bbbe1b4-dd60-42f0-ab21-970f932e6b6a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_subgraph_ef7530ea_repair2
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_hereditary_ef7530ea_repair2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      (∀ u v, N.Adj u v → M.Adj u v) ∧
      (HasPlanarDrawingOn M ∧
        ∀ M' : SimpleGraph V,
          (∀ u v, M.Adj u v → M'.Adj u v) →
          HasPlanarDrawingOn M' →
          ∀ u v, M'.Adj u v → M.Adj u v) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_of_hereditary_ef7530ea_repair2
    HasPlanarDrawingOn
    (fun G H hGH hH =>
      WilliamsonShmoys.planar_drawing_edge_subgraph_ef7530ea_repair2 G H hGH hH)
    N hNdraw