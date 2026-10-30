-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_sharp_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:30:51.604803+00:00
-- url     : https://prove2.me/submissions/45d785ce-07d3-4bf8-a0db-a7d0ed83f519

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
import Theorems.Thm_WilliamsonShmoys_planar_graph_can_add_edge_below_max_count_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> K ≠ H ->
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper : H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589 H hV hH
  by_contra hne
  have hstrict : H.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨K, hHK, hKH, hK⟩ :=
    WilliamsonShmoys.planar_graph_can_add_edge_below_max_count_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589 H hV hH hstrict
  exact hmax K hHK hKH hK