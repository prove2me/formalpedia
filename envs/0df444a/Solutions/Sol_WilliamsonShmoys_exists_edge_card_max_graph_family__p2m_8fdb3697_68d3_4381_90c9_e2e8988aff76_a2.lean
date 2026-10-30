-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_card_max_graph_family__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:50:19.766169+00:00
-- url     : https://prove2.me/submissions/1d7c9fee-8b37-4e72-8be8-1918fed29ade

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (S : SimpleGraph V → Prop) (hS : ∃ G, S G) :
    ∃ M, S M ∧ ∀ N, S N → Set.ncard M.edgeSet ≥ Set.ncard N.edgeSet := by
  classical
  let A : Finset {G : SimpleGraph V // S G} := Finset.univ
  have hA : A.Nonempty := by
    obtain ⟨G, hG⟩ := hS
    exact ⟨⟨G, hG⟩, by simp [A]⟩
  obtain ⟨M, hM, hmax⟩ :=
    Finset.exists_max_image A (fun G => Set.ncard G.1.edgeSet) hA
  refine ⟨M.1, M.2, ?_⟩
  intro N hN
  have hNmem : (⟨N, hN⟩ : {G : SimpleGraph V // S G}) ∈ A := by
    simp [A]
  exact hmax ⟨N, hN⟩ hNmem