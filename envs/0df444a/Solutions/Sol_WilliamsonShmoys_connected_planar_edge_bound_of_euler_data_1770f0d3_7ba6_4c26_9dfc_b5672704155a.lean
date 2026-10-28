-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_of_euler_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:17:47.889668+00:00
-- url     : https://prove2.me/submissions/ab88700f-4512-4bd1-bab4-bf1195c40ec4

import Mathlib

theorem solution {V : Type} [Fintype V] (K : SimpleGraph V) (F : ℕ) (heuler : Fintype.card V + F = K.edgeSet.ncard + 2) (hfaces : 3 * F ≤ 2 * K.edgeSet.ncard) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  omega
