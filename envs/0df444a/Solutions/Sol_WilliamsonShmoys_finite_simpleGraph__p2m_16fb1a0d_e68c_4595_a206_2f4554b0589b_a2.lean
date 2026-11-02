-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:41:10.77213+00:00
-- url     : https://prove2.me/submissions/ce5dd684-62be-4a8b-b98b-7fe3b7aba031

import Mathlib

open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V] : Finite (SimpleGraph V) := by
  classical
  infer_instance
