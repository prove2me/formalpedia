-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_face_data_of_local_edge_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:35:11.409103+00:00
-- url     : https://prove2.me/submissions/716a32e8-e92b-4945-bcf7-98b9c6b92097

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_edge_decomposition
import Theorems.Thm_WilliamsonShmoys_connected_induced_face_data
import Theorems.Thm_WilliamsonShmoys_small_connected_induced_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hlocal : ∀ C : Finset V, C.Nonempty →
      (G.induce (fun v => v ∈ C)).Connected →
      3 ≤ C.card →
      (G.induce (fun v => v ∈ C)).edgeSet.ncard + 6 ≤ 3 * C.card) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard ∧
      (∀ C ∈ parts,
        (G.induce (fun v => v ∈ C)).Connected ∧
        (if 3 ≤ C.card then
          ∃ f : ℕ,
            C.card + f = (G.induce (fun v => v ∈ C)).edgeSet.ncard + 2 ∧
            3 * f ≤ 2 * (G.induce (fun v => v ∈ C)).edgeSet.ncard
        else
          (G.induce (fun v => v ∈ C)).edgeSet.ncard ≤ 3 * C.card - 3)) := by
  obtain ⟨parts, hne, hdisj, hcover, hedge, hconn⟩ :=
    WilliamsonShmoys.connected_component_partition_edge_decomposition G
  refine ⟨parts, hne, hdisj, hcover, hedge, ?_⟩
  intro C hC
  have hCne : C.Nonempty := hne C hC
  have hCconn := hconn C hC
  refine ⟨hCconn, ?_⟩
  by_cases hlarge : 3 ≤ C.card
  · simp only [if_pos hlarge]
    exact WilliamsonShmoys.connected_induced_face_data G C hCne hCconn hlarge
      (hlocal C hCne hCconn hlarge)
  · simp only [if_neg hlarge]
    exact WilliamsonShmoys.small_connected_induced_edge_bound G C hCne hCconn
      (by omega)