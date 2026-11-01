-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:54:06.177818+00:00
-- url     : https://prove2.me/submissions/5aeaedfa-36d8-4807-98c3-082e57eea47e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       W.edgeFinset ⊆ U.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel U.Adj := dU
  have hu := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3 U dU hU hcard
  have hl := WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3 U dU hU hmax hcard
  omega