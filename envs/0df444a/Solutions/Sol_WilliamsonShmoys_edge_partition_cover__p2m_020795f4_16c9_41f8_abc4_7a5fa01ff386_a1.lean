-- Prove2me | solution 1 for WilliamsonShmoys.edge_partition_cover__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:35.358487+00:00
-- url     : https://prove2.me/submissions/532550f9-abd9-4c6a-9652-1ce4588fc459

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hclosed : ∀ u v : V, N.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    C.biUnion (fun s => {e ∈ N.edgeFinset | e.toFinset ⊆ s}) = N.edgeFinset := by
  classical
  letI := dN
  ext e
  constructor
  · intro he
    rcases Finset.mem_biUnion.mp he with ⟨s, hs, hse⟩
    exact (Finset.mem_filter.mp hse).1
  · intro he
    revert he
    refine Sym2.inductionOn e ?_
    intro u v he
    have huv : N.Adj u v := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    obtain ⟨s, hsC, hu, hv⟩ := hclosed u v huv
    apply Finset.mem_biUnion.mpr
    refine ⟨s, hsC, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact huv
    · rw [Sym2.toFinset_mk_eq]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv