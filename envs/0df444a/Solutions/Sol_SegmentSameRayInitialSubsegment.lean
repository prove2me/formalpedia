-- Prove2me | solution 1 for SegmentSameRayInitialSubsegment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:02:19.567124+00:00
-- url     : https://prove2.me/submissions/ab5f6ee3-457f-4187-804a-f1ff80124da5

import Mathlib

open Classical

theorem solution
    (x d : EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hd : d ≠ 0) (ha : 0 < a) :
    ∃ q : EuclideanSpace ℝ (Fin 2),
      x ≠ q ∧
        segment ℝ x q ⊆
          segment ℝ x (x + d) ∩ segment ℝ x (x + a • d) := by
  set t : ℝ := min 1 a with ht
  have ht0 : 0 < t := lt_min one_pos ha
  have ht1 : t ≤ 1 := min_le_left _ _
  have hta : t ≤ a := min_le_right _ _
  refine ⟨x + t • d, ?_, ?_⟩
  · intro h
    have : t • d = 0 := by
      have := congrArg (fun z => z - x) h
      simpa using this.symm
    rcases smul_eq_zero.mp this with h1 | h1
    · exact ht0.ne' h1
    · exact hd h1
  · apply Set.subset_inter
    · apply (convex_segment x (x + d)).segment_subset (left_mem_segment ℝ _ _)
      rw [segment_eq_image']
      exact ⟨t, ⟨ht0.le, ht1⟩, by simp⟩
    · apply (convex_segment x (x + a • d)).segment_subset (left_mem_segment ℝ _ _)
      rw [segment_eq_image']
      refine ⟨t / a, ⟨div_nonneg ht0.le ha.le, (div_le_one ha).mpr hta⟩, ?_⟩
      simp only [add_sub_cancel_left, smul_smul]
      rw [div_mul_cancel₀ t ha.ne']
