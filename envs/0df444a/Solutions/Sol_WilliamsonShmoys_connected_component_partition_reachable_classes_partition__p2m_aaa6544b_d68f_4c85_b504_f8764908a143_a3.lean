-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_reachable_classes_partition__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:45:03.684472+00:00
-- url     : https://prove2.me/submissions/7fd50a55-a32c-4e2e-aa95-2b6d6e4c3791

import Mathlib
open Classical
open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (u v : V) : Finset.univ.filter (fun w => M.Reachable u w) = Finset.univ.filter (fun w => M.Reachable v w) ∨ Disjoint (Finset.univ.filter (fun w => M.Reachable u w)) (Finset.univ.filter (fun w => M.Reachable v w)) := by
  classical
  by_cases h : ∃ w, w ∈ Finset.univ.filter (fun x => M.Reachable u x) ∧
      w ∈ Finset.univ.filter (fun x => M.Reachable v x)
  · obtain ⟨w, hw₁, hw₂⟩ := h
    have huw : M.Reachable u w := (Finset.mem_filter.mp hw₁).2
    have hvw : M.Reachable v w := (Finset.mem_filter.mp hw₂).2
    have huv : M.Reachable u v := huw.trans hvw.symm
    left
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hux
      exact huv.symm.trans hux
    · intro hvx
      exact huv.trans hvx
  · right
    rw [Finset.disjoint_left]
    intro w hw₁ hw₂
    apply h
    exact ⟨w, hw₁, hw₂⟩