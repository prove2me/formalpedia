-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_7802999e_536b_4f03_9f51_584d07594d0b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:12:23.663222+00:00
-- url     : https://prove2.me/submissions/97db4b71-bcc9-4cc5-8528-0b7e61efda43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
       M.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
      L hL
  refine ⟨M, hLM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
    M hV hM hmax