-- Prove2me | solution 1 for WilliamsonShmoys.edge_partition_card__p2m_5190343c_72fe_4ace_a509_b126bd39e3ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:27.131433+00:00
-- url     : https://prove2.me/submissions/8f03eda4-0b72-4376-8238-17539754fa1c

import Mathlib
import Theorems.Thm_WilliamsonShmoys_edge_partition_cover__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
import Theorems.Thm_WilliamsonShmoys_edge_partition_disjoint__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hclosed : ∀ ⦃u v : V⦄, N.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    N.edgeFinset.card = ∑ s ∈ C, {e ∈ N.edgeFinset | e.toFinset ⊆ s}.card := by
  let F : Finset V → Finset (Sym2 V) := fun s => {e ∈ N.edgeFinset | e.toFinset ⊆ s}
  have hdisj : (C : Set (Finset V)).PairwiseDisjoint F := by
    simpa [F] using
      WilliamsonShmoys.edge_partition_disjoint__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
        N dN C hpartition
  have hcover : C.biUnion F = N.edgeFinset := by
    simpa [F] using
      WilliamsonShmoys.edge_partition_cover__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
        N dN C hclosed
  rw [← Finset.card_biUnion hdisj, hcover]