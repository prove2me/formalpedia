-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:15:27.593819+00:00
-- url     : https://prove2.me/submissions/18afd59f-58b1-48e0-b937-823ec8b9c8bb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_9064c577_retry3

open WilliamsonShmoys

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry3
  | (apply _root_.WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry3 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry3 <;> assumption)
