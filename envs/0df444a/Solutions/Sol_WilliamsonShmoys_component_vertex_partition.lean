-- Prove2me | solution 1 for WilliamsonShmoys.component_vertex_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:10:19.939982+00:00
-- url     : https://prove2.me/submissions/d468645b-a2cd-4545-86a3-02a155e7bca7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem S191EY_cvp
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      (∀ u v, G.Adj u v → ∃ C ∈ parts, u ∈ C ∧ v ∈ C) ∧
      (∀ C ∈ parts, (G.induce (fun v => v ∈ C)).Connected) := by
  classical
  have : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let f : G.ConnectedComponent → Finset V := fun c => c.supp.toFinset
  have hf : ∀ c : G.ConnectedComponent, ∀ v, v ∈ f c ↔ G.connectedComponentMk v = c := by
    intro c v
    simp only [f, Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]
  refine ⟨Finset.univ.image f, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro C ⟨c, rfl⟩
    exact ⟨c.out, (hf c _).2 c.out_eq⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro C ⟨c, rfl⟩ D ⟨d, rfl⟩ hne
    rw [Finset.disjoint_left]
    intro v hc hd
    rw [hf] at hc hd
    exact hne (by rw [← hc, ← hd])
  · ext v
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, id, iff_true]
    exact ⟨f (G.connectedComponentMk v), ⟨_, rfl⟩, (hf _ _).2 rfl⟩
  · intro u v huv
    refine ⟨f (G.connectedComponentMk u), Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (hf _ _).2 rfl, (hf _ _).2 ?_⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro C ⟨c, rfl⟩
    have h := (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp c).1
    have hs : (fun v => v ∈ f c : Set V) = c.supp := by
      ext v
      change v ∈ f c ↔ v ∈ c.supp
      rw [hf, SimpleGraph.ConnectedComponent.mem_supp_iff]
    simp only at h
    rw [hs]
    exact h

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      (∀ u v, G.Adj u v → ∃ C ∈ parts, u ∈ C ∧ v ∈ C) ∧
      (∀ C ∈ parts, (G.induce (fun v => v ∈ C)).Connected) :=
  S191EY_cvp G
