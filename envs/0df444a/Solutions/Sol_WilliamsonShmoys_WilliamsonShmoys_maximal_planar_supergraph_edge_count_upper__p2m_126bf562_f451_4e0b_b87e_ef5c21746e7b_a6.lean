-- Prove2me | solution 1 for WilliamsonShmoys.WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:45:11.680071+00:00
-- url     : https://prove2.me/submissions/3169b3c2-31d9-4db4-b50f-62cc37a1204d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P) :
    (letI : DecidableRel P.Adj := Classical.decRel P.Adj;
      P.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel P.Adj := Classical.decRel P.Adj
  have hplanar :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_upper_bound P hP hV
  have hfin : P.edgeFinset.card ≤ P.edgeSet.ncard := by
    exact WilliamsonShmoys.edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
      P P le_rfl
  omega