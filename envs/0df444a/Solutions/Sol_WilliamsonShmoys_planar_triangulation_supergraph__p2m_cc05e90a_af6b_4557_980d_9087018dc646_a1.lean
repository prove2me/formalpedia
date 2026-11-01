-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph__p2m_cc05e90a_af6b_4557_980d_9087018dc646_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:53.388918+00:00
-- url     : https://prove2.me/submissions/4c11153c-6057-4942-9280-36bebb13488a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_supergraph__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj
         N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1 M hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1 N hN hcard hmax