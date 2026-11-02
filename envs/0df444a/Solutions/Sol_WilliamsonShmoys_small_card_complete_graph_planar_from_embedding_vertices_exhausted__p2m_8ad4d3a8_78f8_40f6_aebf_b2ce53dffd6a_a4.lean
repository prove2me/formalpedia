-- Prove2me | solution 1 for WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_vertices_exhausted__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:29.997098+00:00
-- url     : https://prove2.me/submissions/a6bf997c-335c-468d-a1a5-ba9ff4590607

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hsmall : Fintype.card V < 3) (u v : V) (huv : Not (u = v)) :
    ∀ w : V, Or (w = u) (w = v) := by
  intro w
  by_contra hw
  have hwu : w ≠ u := by
    intro h
    exact hw (Or.inl h)
  have hwv : w ≠ v := by
    intro h
    exact hw (Or.inr h)
  let f : Fin 3 → V := fun i => if i = 0 then u else if i = 1 then v else w
  have hinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [f, huv, Ne.symm huv, hwu, Ne.symm hwu, hwv, Ne.symm hwv]
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card V :=
    Fintype.card_le_of_injective f hinj
  simp at hcard
  omega
