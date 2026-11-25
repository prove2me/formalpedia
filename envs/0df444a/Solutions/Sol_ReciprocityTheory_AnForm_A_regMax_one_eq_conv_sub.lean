-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_one_eq_conv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:23.848901+00:00
-- url     : https://prove2.me/submissions/11a422aa-f2c5-4baf-ae22-ed4c15b58804

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_mul_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_integrable
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_integral
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_eq_conv


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
theorem _root_.solution (c : ℝ) :
    regMax (ι := ι) 1 = fun x => convolution kK (fun y => tmax y - c)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x + c := by
  rw [regMax_one_eq_conv]; funext x
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_sub]
  have hi : Integrable (fun s : ι → ℝ => kK s * tmax (x - s)) :=
    (integrable_mul_kK (g := fun s => tmax (x - s))
      (continuous_tmax.comp (continuous_const.sub continuous_id))).congr
      (Eventually.of_forall fun s => mul_comm _ _)
  rw [integral_sub hi (kK_integrable.mul_const c), integral_mul_const, kK_integral]; ring
end ReciprocityTheory.AnForm.A
