-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_has_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:56:36.919986+00:00
-- url     : https://prove2.me/submissions/ab0c790f-19b6-4f69-b6e9-9c427e6cb8ba

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_partial_order_has_maximal_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V → Prop)
    (M : SimpleGraph V)
    (hM : R M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ R N ∧
      ∀ P : SimpleGraph V, N ≤ P → R P → P = N := by
  exact WilliamsonShmoys.finite_partial_order_has_maximal_extension R M hM