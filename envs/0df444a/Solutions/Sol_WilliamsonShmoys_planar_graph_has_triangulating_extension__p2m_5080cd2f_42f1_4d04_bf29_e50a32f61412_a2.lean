-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_5080cd2f_42f1_4d04_bf29_e50a32f61412_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:27:01.046433+00:00
-- url     : https://prove2.me/submissions/150da865-0f0e-4f57-8469-e873511f6d41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      HasPlanarDrawingOn M ∧
      (∀ u v, L.Adj u v → M.Adj u v) ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
       3 * Fintype.card V = M.edgeFinset.card + 6) := by
  obtain ⟨M, hM, hLM, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1
      L hV hL
  refine ⟨M, hM, hLM, ?_⟩
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1
    M hV hM hmax