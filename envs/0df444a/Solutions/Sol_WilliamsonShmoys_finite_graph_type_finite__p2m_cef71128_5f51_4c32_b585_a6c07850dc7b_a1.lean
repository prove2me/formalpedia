-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_type_finite__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:28:10.713217+00:00
-- url     : https://prove2.me/submissions/f4982221-87cf-4808-a121-4a8ce2ed6d23

import Mathlib

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance