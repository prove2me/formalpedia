-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_euler_incidence__p2m_2b14c079_901b_4d89_85a0_5d7005f21dc0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:05:50.730687+00:00
-- url     : https://prove2.me/submissions/8adb31c9-bd40-440f-aca1-e86a369fdf34
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
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
     ∃ f : Nat, Fintype.card V + f = U.edgeFinset.card + 2 ∧
       2 * U.edgeFinset.card = 3 * f) := by
  classical
  letI : DecidableRel U.Adj := dU
  have hupper := WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
    U dU hU hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
    U dU hU hmax hcard
  have hedge : U.edgeFinset.card + 6 = 3 * Fintype.card V :=
    Nat.le_antisymm hupper hlower
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega