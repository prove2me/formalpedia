-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition__p2m_5617b1c6_c5d8_46d6_8dd2_454c2352497f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:41:56.416536+00:00
-- url     : https://prove2.me/submissions/ad74ec9b-54a6-41a3-93b5-de4926f0d8d0

import Theorems.Thm_WilliamsonShmoys_connected_component_partition_class_self__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_reachable_class_connected__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_reachable_classes_partition__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_adj_in_reachable_class__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3

set_option autoImplicit false
open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ v, ∃ C, C ∈ parts ∧ v ∈ C) ∧
      (∀ C, C ∈ parts → C.Nonempty) ∧
      (∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D) ∧
      (∀ u v, M.Adj u v → ∃ C, C ∈ parts ∧ u ∈ C ∧ v ∈ C) ∧
      (∀ C, C ∈ parts → (M.induce (C : Set V)).Connected) := by
  classical
  let cls : V → Finset V := fun v => Finset.univ.filter (fun w => M.Reachable v w)
  let parts : Finset (Finset V) := Finset.univ.image cls
  refine ⟨parts, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    refine ⟨cls v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, ?_⟩
    simpa [cls] using (WilliamsonShmoys.connected_component_partition_class_self__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 M v)
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨v, -, rfl⟩
    exact ⟨v, by simpa [cls] using (WilliamsonShmoys.connected_component_partition_class_self__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 M v)⟩
  · intro C hC D hD hne
    rcases Finset.mem_image.mp hC with ⟨u, -, rfl⟩
    rcases Finset.mem_image.mp hD with ⟨v, -, rfl⟩
    rcases WilliamsonShmoys.connected_component_partition_reachable_classes_partition__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 M u v with heq | hdisj
    · exact (hne heq).elim
    · exact hdisj
  · intro u v huv
    refine ⟨cls u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
    · simpa [cls] using (WilliamsonShmoys.connected_component_partition_class_self__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 M u)
    · simpa [cls] using (WilliamsonShmoys.connected_component_partition_adj_in_reachable_class__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 M huv)
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨v, -, rfl⟩
    exact WilliamsonShmoys.connected_component_partition_reachable_class_connected__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 M v
