-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_convex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:56.19958+00:00
-- url     : https://prove2.me/submissions/97b77c16-d77a-45dc-be0d-cb73e0a6b408

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_convex_comb
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax_shift
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_kK_mono
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_lin_kK

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
theorem _root_.solution (η : ℝ) : ConvexOn ℝ Set.univ (regMax (ι := ι) η) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  rw [regMax_eq_kK, regMax_eq_kK, regMax_eq_kK]
  simp only [smul_eq_mul]
  calc ∫ h, tmax (fun j => (a • x + b • y) j + η * h j) * kK h
        ≤ ∫ h, (a * tmax (fun j => x j + η * h j) + b * tmax (fun j => y j + η * h j)) * kK h := by
          apply integral_kK_mono (continuous_tmax_shift η _)
            ((continuous_const.mul (continuous_tmax_shift η x)).add
              (continuous_const.mul (continuous_tmax_shift η y)))
          intro h _
          have e : (fun j => (a • x + b • y) j + η * h j) =
              a • (fun j => x j + η * h j) + b • (fun j => y j + η * h j) := by
            funext j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            linear_combination (-(η * h j)) * hab
          rw [e]
          exact tmax_convex_comb _ _ ha hb
    _ = a * (∫ h, tmax (fun j => x j + η * h j) * kK h) + b * (∫ h, tmax (fun j => y j + η * h j) * kK h) :=
          integral_lin_kK (continuous_tmax_shift η x) (continuous_tmax_shift η y) a b
end ReciprocityTheory.AnForm.A
