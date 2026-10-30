-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_can_add_edge_below_max_count_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:46:30.585962+00:00
-- url     : https://prove2.me/submissions/e1de304a-43e9-4db2-861a-ca0bd4b04fa3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcount : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K ≠ H ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  by_contra hn
  have hmax : ∀ K : SimpleGraph V, H ≤ K → K ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K := by
    intro K hsub hneq hplanar
    exact hn ⟨K, hsub, hneq, hplanar⟩
  have hbound := WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
    H hV hH hmax
  omega