-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:06:44.668977+00:00
-- url     : https://prove2.me/submissions/daef9e64-e970-4ed3-b737-daf07584c723

import Mathlib

open SimpleGraph

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  classical
  infer_instance