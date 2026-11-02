-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:27.590047+00:00
-- url     : https://prove2.me/submissions/a93db753-86da-4643-ba0f-01dbf3409b09

import Mathlib

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance