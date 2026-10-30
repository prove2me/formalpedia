-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_property_has_maximal_extension__p2m_4274c3cc_8877_4dcd_9fb0_968a87bc56a7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:10.106009+00:00
-- url     : https://prove2.me/submissions/aec9ae04-6132-4c3a-9ca2-ddd3e636f2f1

import Mathlib

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (K : SimpleGraph V)
    (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧ ∀ M : SimpleGraph V, L ≤ M → P M → M = L := by
  classical
  let S : Set (SimpleGraph V) := {L | K ≤ L ∧ P L}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hL⟩ := hSfinite.exists_maximal hSnonempty
  have hLP : K ≤ L ∧ P L := hL.1
  refine ⟨L, hLP.1, hLP.2, ?_⟩
  intro M hLM hPM
  have hM : M ∈ S := ⟨hLP.1.trans hLM, hPM⟩
  have hML : M ≤ L := hL.2 hM hLM
  exact le_antisymm hML hLM