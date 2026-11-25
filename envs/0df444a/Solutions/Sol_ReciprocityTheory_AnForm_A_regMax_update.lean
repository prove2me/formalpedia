-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:11.793791+00:00
-- url     : https://prove2.me/submissions/3355fe91-1404-4d38-84d2-d2e93f7f24dc

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_eq_of_agree
import Theorems.Thm_ReciprocityTheory_AnForm_A_mul_coord_bounds
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_kK_congr

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
theorem _root_.solution [DecidableEq ι] {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ) (j k : ι) (s : ℝ)
    (hkj : k ≠ j) (htj : t j + η ≤ t k) (hs : s + η ≤ t k) :
    regMax η (Function.update t j s) = regMax η t := by
  rw [regMax_eq_kK, regMax_eq_kK]
  apply integral_kK_congr
  intro h hh
  apply tmax_eq_of_agree hkj
  · intro i hi
    show Function.update t j s i + η * h i = t i + η * h i
    first
      | rw [Function.update_of_ne hi]
      | rw [Function.update_noteq hi]
  · show Function.update t j s j + η * h j ≤ Function.update t j s k + η * h k
    first
      | rw [Function.update_self, Function.update_of_ne hkj]
      | rw [Function.update_same, Function.update_noteq hkj]
    linarith [(mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh k).1]
  · show t j + η * h j ≤ t k + η * h k
    linarith [(mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh k).1]
end ReciprocityTheory.AnForm.A
