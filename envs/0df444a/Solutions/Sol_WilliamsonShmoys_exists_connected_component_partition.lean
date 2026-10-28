-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_component_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:11:08.59283+00:00
-- url     : https://prove2.me/submissions/635e39ee-e2d0-4c81-89aa-0e5cf4356e7a

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    ∃ C : Finset (Finset V),
      (∀ v : V, ∃ S, S ∈ C ∧ v ∈ S) ∧
      (∀ S, S ∈ C → ∀ T, T ∈ C → S ≠ T → Disjoint S T) ∧
      (∀ S, S ∈ C → (G.induce (↑S : Set V)).Connected) ∧
      (∀ ⦃u v : V⦄, G.Adj u v → ∃ S, S ∈ C ∧ u ∈ S ∧ v ∈ S) := by
  classical
  let Sf : V → Finset V := fun v =>
    Finset.univ.filter (fun w => G.connectedComponentMk w = G.connectedComponentMk v)
  have hmem : ∀ v w, w ∈ Sf v ↔ G.connectedComponentMk w = G.connectedComponentMk v := by
    intro v w; simp [Sf]
  have hcoe : ∀ v, ((Sf v : Finset V) : Set V) = (G.connectedComponentMk v).supp := by
    intro v; ext w; simp [Sf, SimpleGraph.ConnectedComponent.mem_supp_iff]
  refine ⟨Finset.univ.image Sf, ?_, ?_, ?_, ?_⟩
  · intro v; exact ⟨Sf v, Finset.mem_image_of_mem _ (Finset.mem_univ _), (hmem v v).2 rfl⟩
  · intro S hS T hT hne
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hT
    rw [Finset.disjoint_left]
    intro w hwa hwb
    apply hne
    ext x
    rw [hmem, hmem, ← (hmem a w).1 hwa, (hmem b w).1 hwb]
  · intro S hS
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hS
    rw [hcoe]
    exact (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp _).prop
  · intro u v huv
    refine ⟨Sf u, Finset.mem_image_of_mem _ (Finset.mem_univ _), (hmem u u).2 rfl, (hmem u v).2 ?_⟩
    exact (SimpleGraph.ConnectedComponent.eq.mpr huv.reachable).symm
