-- Prove2me | solution 1 for WilliamsonShmoys.drawable_edgeFinset_card_le_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:27.465468+00:00
-- url     : https://prove2.me/submissions/2f637b47-c617-41a1-a583-9081b30f805a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_connected_edgeFinset_card_le_three_mul_card_sub_six__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
import Theorems.Thm_WilliamsonShmoys_drawable_connected_supergraph__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨G, hsub, hconn, hdraw⟩ :=
    WilliamsonShmoys.drawable_connected_supergraph__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
      M hM hcard
  have hG :=
    WilliamsonShmoys.drawable_connected_edgeFinset_card_le_three_mul_card_sub_six__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
      G hdraw hconn hcard
  have hmono : M.edgeFinset.card ≤ G.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)
  omega