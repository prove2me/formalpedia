-- Prove2me | solution 1 for ThreeSum.Switch.switch_ratio_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:02:13.063324+00:00
-- url     : https://prove2.me/submissions/73677cdb-65b4-46ea-b0f0-008a359b2a77

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_switchIndex_spec
import Theorems.Thm_ThreeSum_Switch_ratio_mem_half

set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    (switchIndex J j r : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) :=
  ratio_mem_half hr (switchIndex_spec hJ hj hr heven).1
end ThreeSum.Switch
