-- Prove2me | solution 1 for WilliamsonShmoys.component_blocks_induced_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:15:37.399036+00:00
-- url     : https://prove2.me/submissions/a4c42169-1b54-4d81-ab6a-e8bd0165ff7f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    ∀ C ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)),
      (G.induce (fun v => v ∈ C)).Connected := by
  intro C hC
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hC
  obtain ⟨v, rfl⟩ := hC
  have h := (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp
    (G.connectedComponentMk v)).1
  have hs : (fun x => x ∈ Finset.univ.filter (fun w : V => G.Reachable v w) : Set V) =
      (G.connectedComponentMk v).supp := by
    ext x
    change x ∈ Finset.univ.filter (fun w : V => G.Reachable v w) ↔ x ∈ (G.connectedComponentMk v).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  simp only at h
  rw [hs]
  exact h
