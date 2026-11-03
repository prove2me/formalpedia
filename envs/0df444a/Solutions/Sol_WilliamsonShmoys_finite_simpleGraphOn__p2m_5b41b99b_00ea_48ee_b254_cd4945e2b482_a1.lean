-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:01:27.136168+00:00
-- url     : https://prove2.me/submissions/1fb21d90-59e7-4e9d-b3be-b8ad29a9ffaf

import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_of_fintype

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] : Finite (SimpleGraph V) :=
  WilliamsonShmoys.finite_simpleGraph_of_fintype