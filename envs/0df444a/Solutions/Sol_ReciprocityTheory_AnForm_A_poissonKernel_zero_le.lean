-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poissonKernel_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:45.783809+00:00
-- url     : https://prove2.me/submissions/0031c6dc-4423-4420-a3e3-21c5a3115953

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {r δ : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) (hδ : 0 < δ) (hzw : δ ≤ ‖z - w‖) :
    poissonKernel 0 w z ≤ (r ^ 2 - ‖w‖ ^ 2) / δ ^ 2 := by
  rw [poissonKernel_def]
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  simp only [sub_zero]
  rw [hz]
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hden : δ ^ 2 ≤ ‖z - w‖ ^ 2 := by nlinarith [hzw, hδ]
  first
  | exact div_le_div_of_nonneg_left hnum (pow_pos hδ 2) hden
  | exact div_le_div_of_le_left hnum (pow_pos hδ 2) hden
  | (gcongr; all_goals first | exact hnum | exact hδ.le | exact hzw | exact pow_pos hδ 2)
end ReciprocityTheory.AnForm.A
