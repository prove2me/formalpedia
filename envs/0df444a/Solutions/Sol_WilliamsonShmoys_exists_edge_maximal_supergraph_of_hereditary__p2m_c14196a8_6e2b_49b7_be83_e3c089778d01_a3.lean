-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_supergraph_of_hereditary__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:48:07.001621+00:00
-- url     : https://prove2.me/submissions/73222f76-1291-4620-9a2e-652e6005471f

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_edge_supergraph_of_maximum_edge_cardinality__p2m_39b66288_b9dd_430f_8b7b_434cfc203be4_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (P : SimpleGraph V → Prop)
    (hdown : ∀ (A B : SimpleGraph V) (dA : DecidableRel A.Adj) (dB : DecidableRel B.Adj),
      (letI : DecidableRel A.Adj := dA
       letI : DecidableRel B.Adj := dB
       A.edgeFinset ⊆ B.edgeFinset) → P B → P A)
    (hP : P K) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel H.Adj := dH
       K.edgeFinset ⊆ H.edgeFinset) ∧
      P H ∧
      ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
        P G →
        (letI : DecidableRel H.Adj := dH
         letI : DecidableRel G.Adj := dG
         H.edgeFinset ⊆ G.edgeFinset →
         H.edgeFinset = G.edgeFinset) := by
  rcases WilliamsonShmoys.exists_edge_supergraph_of_maximum_edge_cardinality__p2m_39b66288_b9dd_430f_8b7b_434cfc203be4_a1
      K dK P hP with ⟨H, dH, hKH, hPH, hmax⟩
  refine ⟨H, dH, hKH, hPH, ?_⟩
  intro G dG hPG hHG
  letI : DecidableRel K.Adj := dK
  letI : DecidableRel H.Adj := dH
  letI : DecidableRel G.Adj := dG
  have hKG : K.edgeFinset ⊆ G.edgeFinset := hKH.trans hHG
  have hcard := hmax G dG hPG hKG
  exact Finset.eq_of_subset_of_card_le hHG hcard