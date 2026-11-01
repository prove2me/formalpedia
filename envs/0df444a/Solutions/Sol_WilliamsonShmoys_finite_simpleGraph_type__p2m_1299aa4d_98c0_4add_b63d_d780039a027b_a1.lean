-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_type__p2m_1299aa4d_98c0_4add_b63d_d780039a027b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:46:46.886015+00:00
-- url     : https://prove2.me/submissions/3b5f3ef5-bf89-46fc-a835-2aa4dfc26f14

import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance