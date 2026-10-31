-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:02:07.492925+00:00
-- url     : https://prove2.me/submissions/c17b7ce1-4f68-481f-bf74-2773051ddb62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_drawable_edgeFinset_card_le_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edgeFinset_card_ge_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M) :
    3 * Fintype.card V - 6 = M.edgeFinset.card := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_drawable_edgeFinset_card_ge_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
      M hM hcard hmax
  · exact WilliamsonShmoys.drawable_edgeFinset_card_le_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
      M hM hcard