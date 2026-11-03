-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_universe__p2m_15a542b2_5d3b_464a_bec6_5f7385b1f62b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:55:41.495923+00:00
-- url     : https://prove2.me/submissions/5a1a2386-145b-421f-a47f-b5be7377bf7f

import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
import Mathlib.Combinatorics.SimpleGraph.Basic

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] : Finite (SimpleGraph V) :=
  WilliamsonShmoys.finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1