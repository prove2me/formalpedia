-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:30:28.396989+00:00
-- url     : https://prove2.me/submissions/f08541ee-a896-4442-a2f2-d943cb700250

import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V] : Finite (SimpleGraph V) :=
  WilliamsonShmoys.finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
