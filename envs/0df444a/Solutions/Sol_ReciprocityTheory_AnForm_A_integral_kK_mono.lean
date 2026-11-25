-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_kK_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:13.097043+00:00
-- url     : https://prove2.me/submissions/aaa61f10-753a-4fc8-b76d-eeba33eacf25

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_mul_kK

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
theorem _root_.solution {F G : (ι → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h, kK h ≠ 0 → F h ≤ G h) : ∫ h, F h * kK h ≤ ∫ h, G h * kK h := by
  refine integral_mono (integrable_mul_kK hF) (integrable_mul_kK hG) fun h => ?_
  by_cases hh : kK h = 0
  · simp [hh]
  · exact mul_le_mul_of_nonneg_right (hFG h hh) (kK_nonneg h)
end ReciprocityTheory.AnForm.A
