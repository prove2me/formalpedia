-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:56:22.909024+00:00
-- url     : https://prove2.me/submissions/61b6665b-6f87-414c-94a9-2299175fa90b

import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
import Mathlib.Combinatorics.SimpleGraph.Basic

import Mathlib

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] : Finite (SimpleGraph V) :=
  WilliamsonShmoys.finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1