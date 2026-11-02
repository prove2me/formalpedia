-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_downward_closed__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:56:46.353745+00:00
-- url     : https://prove2.me/submissions/192c6bb9-68dd-4b38-9b14-969922541c5e

import Mathlib
import Theorems.Thm_finite_downward_closed_has_maximal_extension__p2m_10545618_b4b5_4074_9cf5_b3ff4c8d7112_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {H K : SimpleGraph V}, H ≤ K → P K → P H)
    (G : SimpleGraph V) (hG : P G) :
    ∃ Q : SimpleGraph V,
      G ≤ Q ∧ P Q ∧
        ∀ R : SimpleGraph V, Q ≤ R → P R → R ≤ Q := by
  exact finite_downward_closed_has_maximal_extension__p2m_10545618_b4b5_4074_9cf5_b3ff4c8d7112_a1
    P hdown G hG