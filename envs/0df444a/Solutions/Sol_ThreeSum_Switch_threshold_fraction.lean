-- Prove2me | solution 1 for ThreeSum.Switch.threshold_fraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:28.108507+00:00
-- url     : https://prove2.me/submissions/7d7bb14d-53ad-4b32-8f9f-59adea87d738

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch

set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {J j : ℕ} (hJ : 0 < J) (hj : j < J) :
    switchThreshold ((j : ℝ) / J) =
      (291 * (J : ℝ) + 1000 * j) / (1000 * ((J - j : ℕ) : ℝ)) := by
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hd : ((J - j : ℕ) : ℝ) = (J : ℝ) - j := by
    exact Nat.cast_sub hj.le
  have hden : (J : ℝ) - j ≠ 0 := by
    have hlt : (j : ℝ) < J := by exact_mod_cast hj
    linarith
  rw [hd]
  unfold switchThreshold boxSaving bandShift
  field_simp
  <;> ring
end ThreeSum.Switch
