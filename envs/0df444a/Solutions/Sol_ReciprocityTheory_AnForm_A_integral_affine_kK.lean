-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_affine_kK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:41.506246+00:00
-- url     : https://prove2.me/submissions/7641256d-cba4-40e7-88f1-e0ea294b2228

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_integral
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_mul_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_coord_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_integrable

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
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (c a : ℝ) (i : ι) : ∫ h, (c + a * h i) * kK h = c := by
  have e : (fun h : ι → ℝ => (c + a * h i) * kK h) = fun h => c * kK h + a * (h i * kK h) := by
    funext h
    ring
  rw [e, integral_add (kK_integrable.const_mul c) ((integrable_mul_kK (continuous_apply i)).const_mul a)]
  first
    | rw [integral_const_mul, integral_const_mul]
    | rw [integral_mul_left, integral_mul_left]
  rw [kK_integral, integral_coord_kK]
  ring
end ReciprocityTheory.AnForm.A
