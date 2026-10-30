-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_type__p2m_bf001e0e_24f9_43c1_8004_bdc368085703_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:15.31774+00:00
-- url     : https://prove2.me/submissions/8e4edcd2-ca94-4db8-8426-bb4e3549f771

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V] : Finite (SimpleGraph V) := by
  infer_instance