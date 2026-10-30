-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:50:34.13916+00:00
-- url     : https://prove2.me/submissions/a4ab4f43-9958-4bab-b116-c45b7e25c891

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_for_maximal_drawing_20261026
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_for_maximal_edge_count_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall P : SimpleGraph V, N <= P -> WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_bound_for_maximal_drawing_20261026 N hV hN
  have hlower : 3 * Fintype.card V - 6 <= N.edgeSet.ncard := by
    by_contra h
    have hsmall : N.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
    obtain ⟨P, hNP, hPN, hP⟩ :=
      WilliamsonShmoys.planar_drawing_edge_augmentation_for_maximal_edge_count_20261026 N hV hN hsmall
    have hEq := hmax P hNP hP
    exact hPN hEq
  omega