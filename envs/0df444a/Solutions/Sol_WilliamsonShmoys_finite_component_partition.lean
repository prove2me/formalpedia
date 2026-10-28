-- Prove2me | solution 1 for WilliamsonShmoys.finite_component_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:53.552835+00:00
-- url     : https://prove2.me/submissions/c80a509c-8873-4701-b60c-a05ee485bbb4

import Mathlib

set_option autoImplicit false


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) :
    ∃ C : Finset (Finset V),
      (∀ S ∈ C, S.Nonempty) ∧
      (∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S) ∧
      (∀ ⦃u v : V⦄, H.Adj u v → ∃ S ∈ C, u ∈ S ∧ v ∈ S) ∧
      (∀ S ∈ C, (H.induce (↑S : Set V)).Connected) := by
  classical
  refine ⟨Finset.univ.image (fun c : H.ConnectedComponent => c.supp.toFinset), ?_, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hS
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v, by simp [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩
  · intro v
    refine ⟨(H.connectedComponentMk v).supp.toFinset,
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, by
        simp [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩, ?_⟩
    rintro S ⟨hS, hv⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hS
    simp only [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff] at hv
    rw [hv]
  · intro u v h
    refine ⟨(H.connectedComponentMk u).supp.toFinset,
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, by
        simp [SimpleGraph.ConnectedComponent.mem_supp_iff], ?_⟩
    simp only [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.eq.2 h.reachable).symm
  · intro S hS
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hS
    rw [Set.coe_toFinset]
    exact c.connected_toSimpleGraph
