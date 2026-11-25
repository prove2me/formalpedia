-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tmax_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:55.711944+00:00
-- url     : https://prove2.me/submissions/bb1c5b33-223a-412b-bdba-166c9c1a4759

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_tmax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (t : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) : tmax (c • t) = c * tmax t := by
  apply le_antisymm
  · refine tmax_le fun j => ?_
    show c * t j ≤ c * tmax t
    exact mul_le_mul_of_nonneg_left (le_tmax t j) hc
  · obtain ⟨i, hi⟩ := exists_tmax t
    rw [hi]
    exact le_tmax (c • t) i
end ReciprocityTheory.AnForm.A
