-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_repair3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:03:24.116466+00:00
-- url     : https://prove2.me/submissions/ed5356e6-71e3-492f-b98b-9648e29207b4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_augment_sparse_planar_graph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V,
      HasPlanarDrawingOn U →
      (∀ u v, T.Adj u v → U.Adj u v) →
      (∀ u v, U.Adj u v → T.Adj u v)) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  by_contra hbound
  have hsparse : T.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨U, hU, hTU, ⟨u, v, hnot, hnew⟩⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_augment_sparse_planar_graph
      T hT hCard hsparse
  have hUT := hmax U hU hTU
  exact hnot (hUT u v hnew)