-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMaxLevi_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:09.238484+00:00
-- url     : https://prove2.me/submissions/69af6f57-80eb-450c-826f-59f89ca932a4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv2_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_clm_apply_eq_sum

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
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : RegMaxLeviStatement := by
  intro D ι _ _ η U u hU hη hu z hz w g hg
  classical
  unfold levi
  rw [regMax_comp_fderiv2 hη hU hu hz w, regMax_comp_fderiv2 hη hU hu hz (Complex.I • w),
    clm_apply_eq_sum (fderiv ℝ (regMax (ι := ι) η) (fun j => u j z)),
    clm_apply_eq_sum (fderiv ℝ (regMax (ι := ι) η) (fun j => u j z))]
  have q1 := regMax_fderiv2_nonneg hη (fun j => u j z) (fun j => fderiv ℝ (u j) z w)
  have q2 := regMax_fderiv2_nonneg hη (fun j => u j z) (fun j => fderiv ℝ (u j) z (Complex.I • w))
  have hsum := regMax_fderiv_sum hη (fun j => u j z)
  have h3 : 4 * g ≤ ∑ j, fderiv ℝ (fderiv ℝ (u j)) z w w *
        fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (Pi.single j 1) +
      ∑ j, fderiv ℝ (fderiv ℝ (u j)) z (Complex.I • w) (Complex.I • w) *
        fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (Pi.single j 1) := by
    have e4 : 4 * g = ∑ j, 4 * g * fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (Pi.single j 1) := by
      rw [← Finset.mul_sum, hsum, mul_one]
    rw [e4, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := hg j
    unfold levi at hj
    have hn := regMax_fderiv_nonneg hη (fun j => u j z) (Pi.single j 1)
      (fun k => by rw [Pi.single_apply]; split_ifs <;> norm_num)
    nlinarith
  linarith
end ReciprocityTheory.AnForm.A
