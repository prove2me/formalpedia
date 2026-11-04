-- Prove2me | solution 1 for ThreeSum.Switch.terminal_fraction_exact_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:16.012921+00:00
-- url     : https://prove2.me/submissions/1f9e908c-c841-4728-a6d5-66d1ea72d4ae

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
import Theorems.Thm_ThreeSum_Scales_blockCount_multiple_twenty


set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {n : ℕ} (hmu : 0 < mu n) :
    (terminalDepth n : ℝ) / blockCount (inputBits n) = terminalFraction := by
  have hm := hmu
  rw [actual_totalSize] at hm
  have hJ := Nat.pos_of_mul_pos_right hm
  have hd : 20 ∣ 13 * blockCount (inputBits n) :=
    dvd_mul_of_dvd_right (blockCount_multiple_twenty (inputBits n)) _
  have hid := Nat.div_mul_cancel hd
  have hidR : (terminalDepth n : ℝ) * 20 = 13 * (blockCount (inputBits n) : ℝ) := by
    exact_mod_cast hid
  have hJR : (blockCount (inputBits n) : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  unfold terminalFraction
  field_simp
  linarith
end ThreeSum.Switch
