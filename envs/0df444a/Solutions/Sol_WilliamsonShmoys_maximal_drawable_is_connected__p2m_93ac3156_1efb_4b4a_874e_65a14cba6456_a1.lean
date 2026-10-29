-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_is_connected__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:57:01.462717+00:00
-- url     : https://prove2.me/submissions/83cf8fe7-7ea2-4aff-b0c0-7504cc5f7ac4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_disconnected__p2m_9bb32eb0_a144_4276_9cbf_a7f4026975ff_a2
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hP : HasPlanarDrawingOn P)
    (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) :
    P.Connected := by
  by_contra hNot
  obtain ⟨Q, hPQ, hQdraw, hNotQP⟩ :=
    WilliamsonShmoys.planar_drawing_add_edge_for_disconnected__p2m_9bb32eb0_a144_4276_9cbf_a7f4026975ff_a2
      P hP hNot
  exact hNotQP (hMax Q hPQ hQdraw)
