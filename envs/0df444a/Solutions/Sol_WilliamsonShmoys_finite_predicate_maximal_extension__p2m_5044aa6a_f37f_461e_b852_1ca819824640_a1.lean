-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_maximal_extension__p2m_5044aa6a_f37f_461e_b852_1ca819824640_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:36:50.537276+00:00
-- url     : https://prove2.me/submissions/8f27baee-d96e-4095-a2c3-7cc8cd45538c

import Mathlib
import Theorems.Thm_finite_preorder_has_maximal_element__p2m_781dd872_d82b_41cd_92b7_3c4cf55153dd_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V)
    (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      P N ∧
      ∀ Q : SimpleGraph V, N ≤ Q → P Q → Q = N := by
  classical
  let S : Set (SimpleGraph V) := {N | M ≤ N ∧ P N}
  have hS : S.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hN, hmax⟩ :=
    finite_preorder_has_maximal_element__p2m_781dd872_d82b_41cd_92b7_3c4cf55153dd_a1 S hS
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro Q hNQ hPQ
  have hQ : Q ∈ S := ⟨le_trans hN.1 hNQ, hPQ⟩
  exact le_antisymm (hmax Q hNQ hQ) hNQ