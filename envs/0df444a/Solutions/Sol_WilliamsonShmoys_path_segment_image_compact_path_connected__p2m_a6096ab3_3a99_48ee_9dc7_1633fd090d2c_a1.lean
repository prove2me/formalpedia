-- Prove2me | solution 1 for WilliamsonShmoys.path_segment_image_compact_path_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:04.314395+00:00
-- url     : https://prove2.me/submissions/1423c4a7-2a9b-46ed-80a3-4023399e8831

import Mathlib

theorem solution (γ : ℝ → ℝ × ℝ) (hcont : ContinuousOn γ (Set.Icc 0 1)) :
    IsCompact (γ '' Set.Icc 0 1) ∧ IsPathConnected (γ '' Set.Icc 0 1) := by
  constructor
  · exact isCompact_Icc.image_of_continuousOn hcont
  · exact IsPathConnected.image'
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num, by norm_num⟩) hcont