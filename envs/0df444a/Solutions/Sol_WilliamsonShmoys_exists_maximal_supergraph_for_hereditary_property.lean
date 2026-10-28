-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_hereditary_property
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:43:20.954592+00:00
-- url     : https://prove2.me/submissions/cbbb31a2-203f-41d5-b33b-557571939d94

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hher : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (U : SimpleGraph V) (hU : P U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧ P W ∧
        (∀ X : SimpleGraph V, W ≤ X → P X → X ≤ W) := by
  classical
  obtain ⟨W, hUW, hmax⟩ := Finite.exists_le_maximal hU
  refine ⟨W, hUW, hmax.prop, ?_⟩
  intro X hWX hX
  exact le_of_eq (hmax.eq_of_le hX hWX).symm