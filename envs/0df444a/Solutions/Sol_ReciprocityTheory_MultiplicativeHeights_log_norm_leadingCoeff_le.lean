-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.log_norm_leadingCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:23.04612+00:00
-- url     : https://prove2.me/submissions/5e1187d2-8abb-4501-b606-fff1b097cbb6

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℂ[X]) : Real.log ‖p.leadingCoeff‖ ≤ p.logMahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  rw [logMahlerMeasure_eq_log_MahlerMeasure]
  exact Real.log_le_log (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp))
    (leadingCoeff_le_mahlerMeasure p)
end ReciprocityTheory.MultiplicativeHeights
