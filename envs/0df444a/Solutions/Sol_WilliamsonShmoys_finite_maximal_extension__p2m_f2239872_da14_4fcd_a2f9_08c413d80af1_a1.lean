-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_f2239872_da14_4fcd_a2f9_08c413d80af1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:37.868164+00:00
-- url     : https://prove2.me/submissions/687a5734-8115-4f58-88a5-8a8bebf6efc4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_finite_order__p2m_fe6ffdb7_db07_4cee_9965_0cee09c3b00f_a1

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K ≤ H := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  exact WilliamsonShmoys.exists_maximal_extension_finite_order__p2m_fe6ffdb7_db07_4cee_9965_0cee09c3b00f_a1
    P G hG