-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_finite_graph_predicate__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:29:40.73598+00:00
-- url     : https://prove2.me/submissions/ebdd9ccb-5c48-4c20-8cd9-d568496b0f30

import Theorems.Thm_WilliamsonShmoys_finite_predicate_supergraph_max_edge__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1
import Theorems.Thm_WilliamsonShmoys_strict_graph_extension_edge_ncard__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V)
    (hP : P H)
    (hereditary : ∀ ⦃G K : SimpleGraph V⦄, G ≤ K → P K → P G) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by
  obtain ⟨K, hHK, hPK, hmax⟩ :=
    WilliamsonShmoys.finite_predicate_supergraph_max_edge__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1 P H hP hereditary
  refine ⟨K, hHK, hmax H le_rfl hP, hPK, ?_⟩
  intro L hKL hPL
  by_contra hne
  have hneq : K ≠ L := fun h => hne h.symm
  have hlt : K < L := lt_of_le_of_ne hKL hneq
  have hcount :=
    WilliamsonShmoys.strict_graph_extension_edge_ncard__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1 hlt
  exact (not_lt_of_ge (hmax L (le_trans hHK hKL) hPL) hcount)