-- Prove2me | solution 1 for WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:46:38.57761+00:00
-- url     : https://prove2.me/submissions/99fb0c77-2efa-484e-8025-1fd03085ee11

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_on_finite_vertex_type

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_on_finite_vertex_type
    (P := WilliamsonShmoys.HasPlanarDrawingOn) N hDrawing
