-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tmax_sub_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:00.678725+00:00
-- url     : https://prove2.me/submissions/ea61817c-ea2c-4442-b3c2-52b348da7354

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
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
theorem _root_.solution (s t : ι → ℝ) : tmax s - tmax t ≤ ‖s - t‖ := by
  obtain ⟨i, hi⟩ := exists_tmax s
  rw [hi]
  have h1 := le_tmax t i
  have h2 : ‖(s - t) i‖ ≤ ‖s - t‖ := norm_le_pi_norm (s - t) i
  rw [Pi.sub_apply, Real.norm_eq_abs] at h2
  have h3 := le_abs_self (s i - t i)
  linarith
end ReciprocityTheory.AnForm.A
