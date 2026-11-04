-- Prove2me | solution 1 for ThreeSum.Switch.actual_residual_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:32.657334+00:00
-- url     : https://prove2.me/submissions/317f721c-25a2-4f2f-80ed-5b8497998eca

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_depth_lt
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition

set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {n j : ℕ} (hmu : 0 < mu n) (hj : j ≤ terminalDepth n) :
    0 < residualSize n j := by
  rw [actual_totalSize] at hmu
  have hp := And.intro (Nat.pos_of_mul_pos_right hmu) (Nat.pos_of_mul_pos_left hmu)
  have hd := depth_lt hp.1 (actual_depth_condition hj)
  exact Nat.mul_pos (Nat.sub_pos_of_lt hd) hp.2
end ThreeSum.Switch
