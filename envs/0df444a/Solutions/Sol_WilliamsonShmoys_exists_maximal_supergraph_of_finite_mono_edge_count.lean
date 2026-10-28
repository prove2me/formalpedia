-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_mono_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:52:23.079316+00:00
-- url     : https://prove2.me/submissions/1203b298-644a-41ab-b09a-447899ed1b60

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_admissible_maximal_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hmono : ∀ {G F : SimpleGraph V}, G ≤ F → P F → P G)
    (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  classical
  obtain ⟨K, hHK, hPK, hmax⟩ :=
    WilliamsonShmoys.exists_admissible_maximal_supergraph P H hH
  exact ⟨K, hHK, hPK, Set.ncard_mono (SimpleGraph.edgeSet_mono hHK), hmax⟩