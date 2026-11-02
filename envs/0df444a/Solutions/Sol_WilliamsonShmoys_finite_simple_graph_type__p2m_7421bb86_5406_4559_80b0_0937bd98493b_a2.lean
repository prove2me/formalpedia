-- Prove2me | solution 1 for WilliamsonShmoys.finite_simple_graph_type__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:22.044205+00:00
-- url     : https://prove2.me/submissions/d4e59cf0-598b-49d1-8a27-889592702f39

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance