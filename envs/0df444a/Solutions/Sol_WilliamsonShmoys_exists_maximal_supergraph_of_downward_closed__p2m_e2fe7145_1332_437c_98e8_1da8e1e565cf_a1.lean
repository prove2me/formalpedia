-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_downward_closed__p2m_e2fe7145_1332_437c_98e8_1da8e1e565cf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:57:11.308035+00:00
-- url     : https://prove2.me/submissions/67d641ab-d17f-4b27-939f-5199a693a29c

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G.edgeSet ⊆ H.edgeSet → P H → P G)
    (L : SimpleGraph V) (hL : P L) :
    ∃ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet ∧ P K ∧
      (∀ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet → P J →
        J.edgeSet ⊆ K.edgeSet) := by
  obtain ⟨K, hLK, hKmax⟩ := Finite.exists_le_maximal hL
  refine ⟨K, SimpleGraph.edgeSet_subset_edgeSet.mpr hLK, hKmax.1, ?_⟩
  intro J hKJ hPJ
  have hKJ' : K ≤ J := SimpleGraph.edgeSet_subset_edgeSet.mp hKJ
  exact SimpleGraph.edgeSet_subset_edgeSet.mpr (hKmax.2 hPJ hKJ')