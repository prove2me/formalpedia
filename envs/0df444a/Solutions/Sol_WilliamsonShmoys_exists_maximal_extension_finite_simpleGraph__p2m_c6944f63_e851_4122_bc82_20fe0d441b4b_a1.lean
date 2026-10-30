-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_finite_simpleGraph__p2m_c6944f63_e851_4122_bc82_20fe0d441b4b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:16.344935+00:00
-- url     : https://prove2.me/submissions/11df6455-1182-4700-b0d0-7c348bcf1eec

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hP : P G) : ∃ M : SimpleGraph V, G ≤ M ∧ P M ∧ ∀ H : SimpleGraph V, M ≤ H → P H → H = M := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun H => G ≤ H ∧ P H
  have hS : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hP]
  obtain ⟨M, hM, hmax⟩ :=
    Finset.exists_max_image S (fun H : SimpleGraph V => H.edgeFinset.card) hS
  rcases Finset.mem_filter.mp hM with ⟨_, hGM, hPM⟩
  refine ⟨M, hGM, hPM, ?_⟩
  intro H hMH hPH
  have hGH : G ≤ H := le_trans hGM hMH
  have hHS : H ∈ S := by
    simp [S, hGH, hPH]
  have hcard : H.edgeFinset.card ≤ M.edgeFinset.card := hmax H hHS
  by_contra hne
  have hlt : M.edgeFinset.card < H.edgeFinset.card := by
    apply Finset.card_lt_card
    exact SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr
      (lt_of_le_of_ne hMH (Ne.symm hne))
  omega