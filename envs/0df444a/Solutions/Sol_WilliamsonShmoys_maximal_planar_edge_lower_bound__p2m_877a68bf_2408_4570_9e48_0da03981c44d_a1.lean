-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:15:45.419023+00:00
-- url     : https://prove2.me/submissions/f649b548-ed54-47cf-8fa9-d7f5bc7b2291
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_of_small_card__p2m_6f7b33c7_a7c9_44db_bbb3_dcbcd538e90d_a1
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
     3 * Fintype.card V ≤ U.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel U.Adj := dU
  by_contra hbound
  have hsmall : U.edgeFinset.card + 6 < 3 * Fintype.card V := by omega
  obtain ⟨W, dW, hW, hUW, hnotWU⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_of_small_card__p2m_6f7b33c7_a7c9_44db_bbb3_dcbcd538e90d_a1
      U dU hU hcard hsmall
  exact hnotWU (hmax W dW hW hUW)
