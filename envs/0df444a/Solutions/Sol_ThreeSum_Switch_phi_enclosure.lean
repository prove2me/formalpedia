-- Prove2me | solution 1 for ThreeSum.Switch.phi_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:25.63983+00:00
-- url     : https://prove2.me/submissions/4deda4f0-3802-4388-947e-7f016c720785

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_depth_lt
import Theorems.Thm_ThreeSum_Switch_accepts_iff
import Theorems.Thm_ThreeSum_Switch_switchIndex_spec
import Theorems.Thm_ThreeSum_Switch_switchIndex_pos
import Theorems.Thm_ThreeSum_Switch_predecessor_rejected
import Theorems.Thm_ThreeSum_Switch_ratio_mem_half
import Theorems.Thm_ThreeSum_Switch_switch_ratio_mem
import Theorems.Thm_ThreeSum_Parameters_phi_step_rounding


set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    switchThreshold ((j : ℝ) / J) ≤ phi ((switchIndex J j r : ℝ) / r) ∧
      phi ((switchIndex J j r : ℝ) / r) <
        switchThreshold ((j : ℝ) / J) + 9 / r := by
  have hlt := depth_lt hJ hj
  have hspec := switchIndex_spec hJ hj hr heven
  constructor
  · exact (accepts_iff hJ hlt hr).mp hspec.2
  · have hpos := switchIndex_pos hJ hj hr heven
    have hpre : phi (((switchIndex J j r - 1 : ℕ) : ℝ) / r) <
        switchThreshold ((j : ℝ) / J) := by
      apply lt_of_not_ge
      intro ha
      exact predecessor_rejected hJ hj hr heven ((accepts_iff hJ hlt hr).mpr ha)
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hpR : ((switchIndex J j r - 1 : ℕ) : ℝ) = (switchIndex J j r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    apply phi_step_rounding
      (ratio_mem_half hr (show switchIndex J j r - 1 ≤ r / 2 by omega))
      (switch_ratio_mem hJ hj hr heven) hrR ?_ hpre
    rw [hpR]
    field_simp
    <;> ring
end ThreeSum.Switch
