-- Prove2me | solution 1 for WilliamsonShmoys.path_segment_image_locally_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:30:30.460367+00:00
-- url     : https://prove2.me/submissions/42145fd4-9b44-4e58-add4-6411f101e891

import Mathlib
import Theorems.Thm_locallyConnectedSpace_image_Icc_of_continuousOn__p2m_430e83e9_913b_40ed_87cc_0e4a575c7435_a1

theorem solution
    (γ : ℝ → ℝ × ℝ) (hcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1)) :
    LocallyConnectedSpace (γ '' Set.Icc (0 : ℝ) 1) := by
  exact locallyConnectedSpace_image_Icc_of_continuousOn__p2m_430e83e9_913b_40ed_87cc_0e4a575c7435_a1 γ hcont