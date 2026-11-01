-- Prove2me | solution 1 for WilliamsonShmoys.edge_partition_disjoint__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:46.883194+00:00
-- url     : https://prove2.me/submissions/a604e9e3-51b7-4773-ab85-2b3f54c608a8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s) :
    (C : Set (Finset V)).PairwiseDisjoint
      (fun s => {e ∈ N.edgeFinset | e.toFinset ⊆ s}) := by
  classical
  intro s hs t ht hst
  change Disjoint
    {e ∈ N.edgeFinset | e.toFinset ⊆ s}
    {e ∈ N.edgeFinset | e.toFinset ⊆ t}
  rw [Finset.disjoint_left]
  intro e he het
  have hes := Finset.mem_filter.mp he
  have hets := Finset.mem_filter.mp het
  have hend : e.toFinset.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e)
  obtain ⟨v, hv⟩ := hend
  obtain ⟨u, huC, hu_unique⟩ := hpartition v
  have hsu : s = u := hu_unique s ⟨hs, hes.2 hv⟩
  have htu : t = u := hu_unique t ⟨ht, hets.2 hv⟩
  exact hst (hsu.trans htu.symm)