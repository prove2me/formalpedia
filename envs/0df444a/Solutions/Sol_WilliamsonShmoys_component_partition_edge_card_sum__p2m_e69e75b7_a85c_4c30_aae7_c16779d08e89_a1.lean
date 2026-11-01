-- Prove2me | solution 1 for WilliamsonShmoys.component_partition_edge_card_sum__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:54.364199+00:00
-- url     : https://prove2.me/submissions/ddeb10ae-5c17-4068-b5b4-68093ca66a33

import Mathlib
import Theorems.Thm_WilliamsonShmoys_edge_partition_card__p2m_5190343c_72fe_4ace_a509_b126bd39e3ca_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hclosed : ∀ ⦃u v : V⦄, N.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card := by
  letI := dN
  simpa only [SimpleGraph.card_filter_edgeFinset_toFinset_subset] using
    WilliamsonShmoys.edge_partition_card__p2m_5190343c_72fe_4ace_a509_b126bd39e3ca_a1
      N dN C hpartition hclosed