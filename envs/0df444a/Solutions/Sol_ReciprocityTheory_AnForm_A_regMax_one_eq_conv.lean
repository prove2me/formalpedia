-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_one_eq_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:07.429451+00:00
-- url     : https://prove2.me/submissions/511dbf84-2bce-4136-879e-7614bc04f1bb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_neg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK

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
theorem _root_.solution :
    regMax (ι := ι) 1 = convolution kK tmax (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [regMax_eq_kK]
  first
    | rw [convolution_def]
    | unfold convolution
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have e := integral_neg_eq_self (fun h : ι → ℝ => tmax (fun j => x j + 1 * h j) * kK h) volume
  rw [← e]
  congr 1
  funext h
  show tmax (fun j => x j + 1 * (-h) j) * kK (-h) = kK h * tmax (x - h)
  rw [kK_neg, mul_comm (tmax (fun j => x j + 1 * (-h) j)) (kK h)]
  congr 2
  funext j
  simp only [Pi.sub_apply, Pi.neg_apply]
  ring
end ReciprocityTheory.AnForm.A
