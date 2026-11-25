-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_lin_kK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:50.46898+00:00
-- url     : https://prove2.me/submissions/b8835780-a740-4769-8b31-fe41c5117f1c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
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
theorem _root_.solution {F G : (ι → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G) (a b : ℝ) :
    ∫ h, (a * F h + b * G h) * kK h = a * (∫ h, F h * kK h) + b * (∫ h, G h * kK h) := by
  have e : (fun h => (a * F h + b * G h) * kK h) = fun h => a * (F h * kK h) + b * (G h * kK h) := by
    funext h
    ring
  rw [e, integral_add ((integrable_mul_kK hF).const_mul a) ((integrable_mul_kK hG).const_mul b)]
  first
    | rw [integral_const_mul, integral_const_mul]
    | rw [integral_mul_left, integral_mul_left]
end ReciprocityTheory.AnForm.A
