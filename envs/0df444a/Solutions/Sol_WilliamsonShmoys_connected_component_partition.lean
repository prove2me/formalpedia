-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:49:26.691586+00:00
-- url     : https://prove2.me/submissions/0b8797ef-8036-44ef-8ce6-0a2d35beb3d1

import Mathlib

theorem S181part {V : Type} [Fintype V] (H : SimpleGraph V) :
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

theorem S181small {V : Type} [Fintype V] (H : SimpleGraph V) (S : Finset V) :
    (H.induce (↑S : Set V)).edgeSet.ncard ≤ S.card.choose 2 := by
  classical
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := H.induce (↑S : Set V))
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at h
  simpa using h

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ P : Finset (Finset V),
      (∀ v : V, ∃! S : Finset V, S ∈ P ∧ v ∈ S) ∧
      (∀ S : Finset V, S ∈ P → (G.induce (S : Set V)).Connected) ∧
      (∀ ⦃u v : V⦄, G.Adj u v → ∃ S : Finset V, S ∈ P ∧ u ∈ S ∧ v ∈ S) ∧
      (∀ S : Finset V, S ∈ P → S.card < 3 →
        2 * (G.induce (S : Set V)).edgeSet.ncard ≤ S.card) := by
  classical
  obtain ⟨C, hne, huniq, hcross, hconn⟩ := S181part G
  refine ⟨C, huniq, hconn, hcross, fun S hS h3 => ?_⟩
  have hs := S181small G S
  have hc0 : Nat.choose 0 2 = 0 := rfl
  have hc1 : Nat.choose 1 2 = 0 := rfl
  have hc2 : Nat.choose 2 2 = 1 := rfl
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2) with h | h | h
  · rw [h, hc0] at hs; omega
  · rw [h, hc1] at hs; omega
  · rw [h, hc2] at hs; omega
