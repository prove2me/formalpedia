-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_of_small_card__p2m_6f7b33c7_a7c9_44db_bbb3_dcbcd538e90d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:02:30.4851+00:00
-- url     : https://prove2.me/submissions/ff305368-9bdf-41fc-b5e0-c84474e38280
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V)
    (hsmall : (letI : DecidableRel U.Adj := dU
      U.edgeFinset.card + 6 < 3 * Fintype.card V)) :
    ∃ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W ∧
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) ∧
      ¬ (letI : DecidableRel U.Adj := dU
         letI : DecidableRel W.Adj := dW
         W.edgeFinset ⊆ U.edgeFinset) := by
  obtain ⟨W, dW, hW, hUW, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3 U dU hU
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
      W dW hW hcard hmax
  refine ⟨W, dW, hW, hUW, ?_⟩
  intro hWU
  letI : DecidableRel U.Adj := dU
  letI : DecidableRel W.Adj := dW
  have hlt : U.edgeFinset.card < W.edgeFinset.card := by
    change U.edgeFinset.card + 6 < 3 * Fintype.card V at hsmall
    change 3 * Fintype.card V - 6 ≤ W.edgeFinset.card at hbound
    omega
  have heq : U.edgeFinset.card = W.edgeFinset.card :=
    Nat.le_antisymm (Finset.card_le_card hUW) (Finset.card_le_card hWU)
  omega