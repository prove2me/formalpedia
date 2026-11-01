-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraphOn__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:54.057008+00:00
-- url     : https://prove2.me/submissions/a3f1ceb9-d3b2-4668-a23d-1d9c4181bf82

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] : Finite (SimpleGraph V) := by
  infer_instance