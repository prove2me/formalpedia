-- Prove2me | solution 1 for WilliamsonShmoys.finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:44:01.701819+00:00
-- url     : https://prove2.me/submissions/5ee484cb-56a7-472c-a6b8-eb7d6cf9b3ff

import Theorems.Thm_WilliamsonShmoys_finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2

import Mathlib
set_option autoImplicit false

theorem solution {alpha : Type} [PartialOrder alpha] [Finite alpha] (P : alpha -> Prop) (hP : Exists fun x => P x) : Exists fun x => P x /\ forall y, P y -> LE.le x y -> y = x :=
  WilliamsonShmoys.finite_type_predicate_maximal__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2 P hP
