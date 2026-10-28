-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:06:13.196375+00:00
-- url     : https://prove2.me/submissions/e0fe4a70-f1eb-4017-8315-ce1352a77e31
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → K ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨T, hHT, hTplanar, hTcount⟩ :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589_triangulation_extension
      H hV hH
  have hTH : T = H := by
    by_contra hne
    exact hmax T hHT hne hTplanar
  rw [← hTH]
  exact le_of_eq hTcount