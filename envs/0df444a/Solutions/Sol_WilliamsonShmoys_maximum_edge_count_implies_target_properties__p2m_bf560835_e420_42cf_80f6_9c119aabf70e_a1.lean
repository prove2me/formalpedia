-- Prove2me | solution 1 for WilliamsonShmoys.maximum_edge_count_implies_target_properties__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:28.086799+00:00
-- url     : https://prove2.me/submissions/0a3c7443-cae5-44b1-8448-3ef2c1029489

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_eq_of_inclusion_and_ncard_bound__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L M : SimpleGraph V)
    (hLM : L ≤ M)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       L.edgeFinset.card ≤ M.edgeSet.ncard) := by
  constructor
  · intro N hMN hN
    have hLN : L ≤ N := le_trans hLM hMN
    have hcount : N.edgeSet.ncard ≤ M.edgeSet.ncard := hmax N hLN hN
    exact WilliamsonShmoys.edge_eq_of_inclusion_and_ncard_bound__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
      M N hMN hcount
  · letI : DecidableRel L.Adj := Classical.decRel L.Adj
    exact WilliamsonShmoys.edgeFinset_card_le_supergraph_ncard__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
      L M hLM
