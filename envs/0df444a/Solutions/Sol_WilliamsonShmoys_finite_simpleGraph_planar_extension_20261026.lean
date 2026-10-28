-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_planar_extension_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:03:20.521992+00:00
-- url     : https://prove2.me/submissions/9417992d-7d17-4a92-af5d-31bd9133f64a

import Mathlib

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance