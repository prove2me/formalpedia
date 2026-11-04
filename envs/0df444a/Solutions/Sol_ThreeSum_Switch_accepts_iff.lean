-- Prove2me | solution 1 for ThreeSum.Switch.accepts_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:22.029709+00:00
-- url     : https://prove2.me/submissions/c4f6da69-d587-4546-8871-cd624460d417

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_threshold_fraction
import Theorems.Thm_ThreeSum_Switch_phi_fraction

set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {J j r q : ℕ} (hJ : 0 < J) (hj : j < J) (hr : 0 < r) :
    accepts J j r q ↔ switchThreshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / r) := by
  have hd : (0 : ℝ) < ((J - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [threshold_fraction hJ hj, phi_fraction hr, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : accepts J j r q ↔
      (291 * (J : ℝ) + 1000 * j) * (r : ℝ) ^ 3 ≤
        10 * ((J - j : ℕ) : ℝ) * (cubicNumerator r q : ℝ) := by
    unfold accepts
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith
end ThreeSum.Switch
