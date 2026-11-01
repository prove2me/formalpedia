-- Prove2me | solution 1 for WilliamsonShmoys.component_partition_connected_components__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:15.956633+00:00
-- url     : https://prove2.me/submissions/0403bd72-9dd1-4650-8289-56daa90bfb5b

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj) :
    ∃ C : Finset (Finset V),
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s) ∧
      (∀ s ∈ C, (N.induce (s : Set V)).Connected) ∧
      (∀ ⦃u v : V⦄, N.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) := by
  classical
  letI : DecidableRel N.Adj := dN
  let C : Finset (Finset V) :=
    Finset.univ.image (fun c : N.ConnectedComponent => c.supp.toFinset)
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨c, -, rfl⟩
    rcases SimpleGraph.ConnectedComponent.nonempty_supp c with ⟨v, hv⟩
    exact ⟨v, by simpa using hv⟩
  · intro v
    refine ⟨(N.connectedComponentMk v).supp.toFinset, ?_, ?_⟩
    · simp [C]
    · intro s hs
      have hv : v ∈ s := hs.2
      rcases Finset.mem_image.mp hs.1 with ⟨c, -, rfl⟩
      have hv' : v ∈ c.supp := by simpa using hv
      have hc : c = N.connectedComponentMk v :=
        SimpleGraph.ConnectedComponent.eq_of_common_vertex hv'
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      simpa [hc]
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨c, -, rfl⟩
    have hsupp : ((↑c.supp.toFinset : Finset V) : Set V) = c.supp := by
      ext x
      simp
    rw [hsupp]
    simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using
      (SimpleGraph.ConnectedComponent.connected_toSimpleGraph c)
  · intro u v hadj
    refine ⟨(N.connectedComponentMk u).supp.toFinset, ?_, ?_, ?_⟩
    · simp [C]
    · simp
    · have hu : u ∈ (N.connectedComponentMk u).supp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      have hv : v ∈ (N.connectedComponentMk u).supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_congr_adj
          (N.connectedComponentMk u) hadj).mp hu
      simpa using hv
