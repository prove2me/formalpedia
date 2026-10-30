-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_finite_of_fintype__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:47:47.886252+00:00
-- url     : https://prove2.me/submissions/23a3ca56-c6b8-4ed5-9312-e4403f49b7ba

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance