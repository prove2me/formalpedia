-- Prove2me | solution 1 for WilliamsonShmoys.finite_simple_graph_type__p2m_07123160_8e02_4c14_a3ba_8b97213ab1a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:50.682214+00:00
-- url     : https://prove2.me/submissions/e4f94f38-270d-4cf4-a964-8cc172a0620c

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance
