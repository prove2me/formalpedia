-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_8f423fe5_b3be_4138_81a9_17669ac64a5c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:19:19.682105+00:00
-- url     : https://prove2.me/submissions/e53dca5a-d96e-4816-8f80-8a192c89c523
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_edge_maximal_extension__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_has_euler_edge_count__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    exists H : SimpleGraph V, exists instH : DecidableRel H.Adj,
      (letI : DecidableRel H.Adj := instH
       G.edgeFinset ⊆ H.edgeFinset /\
       HasPlanarDrawingOn H /\
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨H, instH, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.drawable_edge_maximal_extension__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
      G hG hV
  letI : DecidableRel H.Adj := instH
  refine ⟨H, instH, hGH, hH, ?_⟩
  exact WilliamsonShmoys.edge_maximal_drawable_has_euler_edge_count__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
    H hH hMax hV