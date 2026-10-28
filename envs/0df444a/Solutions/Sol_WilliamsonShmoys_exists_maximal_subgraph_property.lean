-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_subgraph_property
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:06:56.914872+00:00
-- url     : https://prove2.me/submissions/64a1a58f-1737-45d9-a091-5db7377a077e

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hP : ∃ G : SimpleGraph V, P G) :
    ∃ L : SimpleGraph V, P L ∧
      ∀ M : SimpleGraph V, P M → L ≤ M → M = L := by
  classical
  obtain ⟨G, hG⟩ := hP
  have hGmem : G ∈ {H : SimpleGraph V | P H} := hG
  obtain ⟨L, hGL, hmax⟩ :=
    (Set.toFinite {H : SimpleGraph V | P H}).exists_le_maximal hGmem
  refine ⟨L, hmax.1, ?_⟩
  intro M hM hLM
  exact le_antisymm (hmax.2 hM hLM) hLM