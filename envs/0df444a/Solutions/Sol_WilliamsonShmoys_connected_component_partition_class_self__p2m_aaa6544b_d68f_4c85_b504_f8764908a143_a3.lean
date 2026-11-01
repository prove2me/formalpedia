-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_class_self__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:46.036869+00:00
-- url     : https://prove2.me/submissions/8d660ca9-bf35-42dc-a935-13cb81570d5b

import Mathlib
open Classical
open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (v : V) : v ∈ Finset.univ.filter (fun w => M.Reachable v w) := by
  simp