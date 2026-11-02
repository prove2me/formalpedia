-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_9358304e_f36c_4627_ac4a_68d95a8f78e3_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:23:34.78891+00:00
-- url     : https://prove2.me/submissions/457a4647-7971-415a-8e57-07a712fd5178
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_05b91864_4011_4912_8401_09994d13f3f6_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_05b91864_4011_4912_8401_09994d13f3f6_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_05b91864_4011_4912_8401_09994d13f3f6_a2
      M hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_05b91864_4011_4912_8401_09994d13f3f6_a2
    N hcard hN hmax