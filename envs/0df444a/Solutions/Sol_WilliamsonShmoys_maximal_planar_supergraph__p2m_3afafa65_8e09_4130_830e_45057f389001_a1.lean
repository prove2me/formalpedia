-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_3afafa65_8e09_4130_830e_45057f389001_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:56.271756+00:00
-- url     : https://prove2.me/submissions/3d52458b-fa93-4711-b3a7-7adb0aac5a0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      (∀ ⦃u v : V⦄, U.Adj u v → W.Adj u v) ∧
      HasPlanarDrawingOn W ∧
      (letI : DecidableRel W.Adj := dW
       W.edgeFinset.card + 6 = 3 * Fintype.card V) ∧
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset.card ≤ W.edgeFinset.card) := by
  obtain ⟨W, dW, hUW, hW, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
      U dU hU
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_ef8dab25_617a_4455_968a_bd2c49e19056_a1
      W dW hW hcard hmax
  letI : DecidableRel U.Adj := dU
  letI : DecidableRel W.Adj := dW
  refine ⟨W, dW, hUW, hW, hcount, ?_⟩
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hUW)
