-- Prove2me | solution 1 for WilliamsonShmoys.finite_simple_graphs__p2m_1ace3c40_0347_471f_a850_5688ff0e5a6a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:11:41.960471+00:00
-- url     : https://prove2.me/submissions/2f0f45e0-b35b-49ee-b1d6-fa034d9b039a

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance