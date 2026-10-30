-- Prove2me | solution 1 for WilliamsonShmoys.path_segment_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:02.56713+00:00
-- url     : https://prove2.me/submissions/4c9cff7b-6fa8-44f1-a7a5-4ed2802e39b7

import Theorems.Thm_WilliamsonShmoys_path_segment_image_compact_path_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
import Theorems.Thm_WilliamsonShmoys_path_segment_image_locally_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1

set_option autoImplicit false

theorem solution
    (γ : ℝ → ℝ × ℝ) (hcont : ContinuousOn γ (Set.Icc 0 1)) :
    IsCompact (γ '' Set.Icc 0 1) ∧
      IsPathConnected (γ '' Set.Icc 0 1) ∧
      LocallyConnectedSpace (γ '' Set.Icc 0 1) := by
  obtain ⟨hcompact, hpath⟩ :=
    WilliamsonShmoys.path_segment_image_compact_path_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
      γ hcont
  have hloc :=
    WilliamsonShmoys.path_segment_image_locally_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
      γ hcont
  exact ⟨hcompact, hpath, hloc⟩