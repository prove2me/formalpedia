-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:10:46.805551+00:00
-- url     : https://prove2.me/submissions/d8b68307-4f74-4e24-82cd-36a098e802be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    N.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨H, hsub, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
      N hN hconn hcard
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
      H hH hmax hcard
  have hmono :=
    WilliamsonShmoys.edgeFinset_card_mono__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
      N H hsub
  omega
