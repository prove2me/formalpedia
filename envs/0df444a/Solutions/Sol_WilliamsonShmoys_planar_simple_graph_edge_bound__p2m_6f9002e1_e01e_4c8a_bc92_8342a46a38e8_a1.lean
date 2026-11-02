-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_6f9002e1_e01e_4c8a_bc92_8342a46a38e8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:41:49.561247+00:00
-- url     : https://prove2.me/submissions/38259535-4975-4992-a38c-8f7226ea2716

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    [decG : DecidableRel G.Adj] :
    G.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  have hbound :=
    WilliamsonShmoys.maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
      G hG hcard
  have hcard_eq :
      (letI : DecidableRel G.Adj := decG; G.edgeFinset.card) =
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.edgeFinset.card) := by
    congr 1
    ext e
    simp [SimpleGraph.edgeFinset]
  have hcard_le_classical :
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.edgeFinset.card) <= G.edgeSet.ncard := by
    exact WilliamsonShmoys.edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
      G G le_rfl
  have hcard_le : G.edgeFinset.card <= G.edgeSet.ncard := by
    rw [hcard_eq]
    exact hcard_le_classical
  omega