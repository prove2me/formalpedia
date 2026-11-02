-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_1cb61011_99ad_4f9a_a1ee_f080a0059de3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:24:33.738494+00:00
-- url     : https://prove2.me/submissions/bc48234c-c6bf-438c-a192-541b2aa4ec90

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    ∃ M : SimpleGraph V, L <= M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
      L hL
  refine ⟨M, hLM, hM, ?_⟩
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hcount : M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
      M hM hcard hmax
  have hcardEq : M.edgeFinset.card = M.edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [hcardEq]
  exact hcount
