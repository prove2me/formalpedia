-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.scaled_phase_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.642233+00:00
-- url     : https://prove2.me/submissions/f4a0621c-f18b-4e54-9981-a391ca3ed3c2

import Theorems.Thm_ZeroFreeRRG_Hardcore_unit_phase_perturbation
import Mathlib
set_option autoImplicit false
open ZeroFreeRRG.Hardcore

theorem solution (z w : ℂ) (r : ℝ) (hz : z ≠ 0)
    (hr0 : 0 ≤ r) (hr : r ≤ 96/625) (hclose : ‖z-w‖ ≤ r*‖z‖) :
    w ≠ 0 ∧ ‖z/(‖z‖:ℂ)-w/(‖w‖:ℂ)‖ ≤ (25/23)*r := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hzc : (‖z‖:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hzpos
  let u := z/(‖z‖:ℂ)
  let v := w/(‖z‖:ℂ)
  have hu : ‖u‖=1 := by
    dsimp [u]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hzpos,div_self (ne_of_gt hzpos)]
  have hc : ‖u-v‖ ≤ r := by
    dsimp [u,v]
    rw [← sub_div,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hzpos]
    exact (div_le_iff₀ hzpos).2 hclose
  have hh := unit_phase_perturbation u v r hu hr0 hr hc
  have hw : w ≠ 0 := by
    intro hw
    have : v=0 := by simp [v,hw]
    exact hh.1 this
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwc : (‖w‖:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hwpos
  have hv : v/(‖v‖:ℂ) = w/(‖w‖:ℂ) := by
    dsimp [v]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hzpos,Complex.ofReal_div]
    field_simp
  exact ⟨hw,by simpa only [hv] using hh.2⟩
