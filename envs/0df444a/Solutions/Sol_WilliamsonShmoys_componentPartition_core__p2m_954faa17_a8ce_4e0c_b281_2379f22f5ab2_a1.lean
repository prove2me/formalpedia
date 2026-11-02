-- Prove2me | solution 1 for WilliamsonShmoys.componentPartition_core__p2m_954faa17_a8ce_4e0c_b281_2379f22f5ab2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:17:10.042833+00:00
-- url     : https://prove2.me/submissions/c638f482-2214-41bc-bb25-62a47dd9da84

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj) :
    letI : DecidableRel L.Adj := dL
    ∃ C : Finset (Finset V),
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) ∧
      (∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) := by
  classical
  letI : DecidableRel L.Adj := dL
  let C : Finset (Finset V) :=
    Finset.univ.image (fun c : L.ConnectedComponent => c.supp.toFinset)
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    change s ∈ Finset.univ.image (fun c : L.ConnectedComponent => c.supp.toFinset) at hs
    rcases Finset.mem_image.mp hs with ⟨c, -, rfl⟩
    obtain ⟨v, hv⟩ := c.nonempty_supp
    exact ⟨v, by simpa using hv⟩
  · intro v
    refine ⟨(L.connectedComponentMk v).supp.toFinset, ?_, ?_⟩
    · change (L.connectedComponentMk v).supp.toFinset ∈
        Finset.univ.image (fun c : L.ConnectedComponent => c.supp.toFinset)
      exact Finset.mem_image.mpr
        ⟨L.connectedComponentMk v, Finset.mem_univ _, rfl⟩
    · simpa using
        (show v ∈ (L.connectedComponentMk v).supp from rfl)
  · intro s hs t ht hne
    change s ∈ Finset.univ.image (fun c : L.ConnectedComponent => c.supp.toFinset) at hs
    change t ∈ Finset.univ.image (fun c : L.ConnectedComponent => c.supp.toFinset) at ht
    rcases Finset.mem_image.mp hs with ⟨c, -, rfl⟩
    rcases Finset.mem_image.mp ht with ⟨d, -, rfl⟩
    have hcd : c ≠ d := by
      intro h
      apply hne
      simpa [h]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Set.disjoint_left.mp
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent L hcd))
      (by simpa using hx) (by simpa using hy)
  · intro s hs
    change s ∈ Finset.univ.image (fun c : L.ConnectedComponent => c.supp.toFinset) at hs
    rcases Finset.mem_image.mp hs with ⟨c, -, rfl⟩
    have hsupp : (↑c.supp.toFinset : Set V) = c.supp := by
      ext x
      simp
    rw [hsupp]
    exact c.connected_toSimpleGraph
  · intro u v huv
    let c : L.ConnectedComponent := L.connectedComponentMk u
    refine ⟨c.supp.toFinset, ?_, ?_⟩
    · change c.supp.toFinset ∈
        Finset.univ.image (fun c : L.ConnectedComponent => c.supp.toFinset)
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
    · constructor
      · have hu : u ∈ c.supp := by
          change L.connectedComponentMk u = c
          rfl
        simpa using hu
      · have hu : u ∈ c.supp := by
          change L.connectedComponentMk u = c
          rfl
        simpa using c.mem_supp_of_adj_mem_supp hu huv
