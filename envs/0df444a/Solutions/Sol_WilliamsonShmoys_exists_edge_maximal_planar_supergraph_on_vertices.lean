-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph_on_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:24:05.111371+00:00
-- url     : https://prove2.me/submissions/8e231536-dca1-482e-ac5d-ff119aeddf85

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_has_edge_maximal_member

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  exact WilliamsonShmoys.finite_graph_has_edge_maximal_member
    WilliamsonShmoys.HasPlanarDrawingOn K hK