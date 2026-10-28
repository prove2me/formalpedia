-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_finite_vertex_type
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:36:35.612392+00:00
-- url     : https://prove2.me/submissions/0bd5e57f-431b-4051-a4ca-e268d6dcdfa8

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (L : SimpleGraph V)
    (hL : P L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G => L ≤ G ∧ P G
  have hS : S.Nonempty := by
    refine ⟨L, ?_⟩
    simp [S, hL]
  obtain ⟨M, hM, hmax⟩ := S.exists_maximal hS
  have hprops : L ≤ M ∧ P M := by
    simpa [S] using hM
  refine ⟨M, hprops.1, hprops.2, ?_⟩
  intro N hMN hPN
  have hLN : L ≤ N := le_trans hprops.1 hMN
  have hN : N ∈ S := by
    simp [S, hLN, hPN]
  exact hmax hN hMN