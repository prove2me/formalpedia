-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_downward_closed__p2m_9a3aed6d_2bec_4e6f_a443_353e67f8b6ae_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:28.847826+00:00
-- url     : https://prove2.me/submissions/9b9dd1e2-62ab-4c98-813d-cfa6a4328f6d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_supergraph_maximal_edgeFinset_cardinality__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_lt_of_le_of_ne__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1

open SimpleGraph

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  obtain ⟨H, hGH, hPH, hHfin, hmax⟩ :=
    WilliamsonShmoys.exists_supergraph_maximal_edgeFinset_cardinality__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
      P hdown G hG
  letI : Fintype H.edgeSet := hHfin
  refine ⟨H, hGH, hPH, ?_⟩
  intro K hHK hPK
  letI : Fintype K.edgeSet := inferInstance
  have hcard := hmax K (le_trans hGH hHK) hPK inferInstance
  by_contra hne
  have hstrict :=
    WilliamsonShmoys.edgeFinset_card_lt_of_le_of_ne__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
      H K hHfin inferInstance hHK (fun h => hne h.symm)
  omega