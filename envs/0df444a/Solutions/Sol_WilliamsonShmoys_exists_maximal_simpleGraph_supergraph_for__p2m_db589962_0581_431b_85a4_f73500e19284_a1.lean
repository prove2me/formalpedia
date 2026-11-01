-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_simpleGraph_supergraph_for__p2m_db589962_0581_431b_85a4_f73500e19284_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:07:09.324812+00:00
-- url     : https://prove2.me/submissions/cb768a81-90e3-49b3-ad30-f23ccfa06975

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (U : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P U) :
    ∃ W : SimpleGraph V, U ≤ W ∧ P W ∧
      ∀ X : SimpleGraph V, W ≤ X → P X → X ≤ W := by
  classical
  let Q : SimpleGraph V → Prop := fun G => U ≤ G ∧ P G
  have hU : Q U := ⟨le_rfl, hP⟩
  obtain ⟨W, hUW, hmax⟩ := Finite.exists_le_maximal hU
  refine ⟨W, hmax.prop.1, hmax.prop.2, ?_⟩
  intro X hWX hPX
  have hQX : Q X := ⟨hmax.prop.1.trans hWX, hPX⟩
  by_contra hXW
  have hne : W ≠ X := by
    intro heq
    subst X
    exact hXW le_rfl
  have hlt : W < X := lt_of_le_of_ne hWX hne
  exact (hmax.not_prop_of_gt hlt) hQX