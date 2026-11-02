-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_predicate_has_edge_max__p2m_5f4c0396_f2c5_4ee4_89c1_d7bcb4050c5c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:25:08.199158+00:00
-- url     : https://prove2.me/submissions/8c8c9408-5d10-4bf3-aec7-d93c1adf884f

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hP : ∃ G, P G) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, P H ∧
      (∀ K : SimpleGraph V, P K → K.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  letI : Fintype {G : SimpleGraph V // P G} := Fintype.ofFinite _
  let s : Finset {G : SimpleGraph V // P G} := Finset.univ
  have hs : s.Nonempty := by
    obtain ⟨G, hG⟩ := hP
    exact ⟨⟨G, hG⟩, Finset.mem_univ _⟩
  obtain ⟨H, hHmem, hHmax⟩ := Finset.exists_max_image s
    (fun G : {G : SimpleGraph V // P G} => G.1.edgeFinset.card) hs
  refine ⟨H.1, H.2, ?_⟩
  intro K hK
  have hKmem : (⟨K, hK⟩ : {G : SimpleGraph V // P G}) ∈ s := by
    simp [s]
  exact hHmax ⟨K, hK⟩ hKmem