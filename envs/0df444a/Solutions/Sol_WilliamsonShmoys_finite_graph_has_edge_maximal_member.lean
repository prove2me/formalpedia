-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_has_edge_maximal_member
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:46:49.404984+00:00
-- url     : https://prove2.me/submissions/18ecd197-0d6b-4a72-a1ce-b99f8774ee14

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧ ∀ M : SimpleGraph V, L ≤ M → P M → M = L := by
  classical
  let S : Set (SimpleGraph V) := {L | K ≤ L ∧ P L}
  have hSfinite : S.Finite := Set.finite_univ.subset (by
    intro L hL
    exact Set.mem_univ L)
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hL, hLmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hPM
  have hM : M ∈ S := ⟨hL.1.trans hLM, hPM⟩
  have hML : M ≤ L := hLmax hM hLM
  exact le_antisymm hML hLM