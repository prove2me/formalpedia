-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_add_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:40:32.734337+00:00
-- url     : https://prove2.me/submissions/93c94edc-2795-42bf-a7a6-886aeeaecdcd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax_shift
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_const_kK
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
theorem _root_.solution (η : ℝ) (t : ι → ℝ) (c : ℝ) :
    regMax η (fun j => t j + c) = regMax η t + c := by
  rw [regMax_eq_kK, regMax_eq_kK]
  have e : ∀ h : ι → ℝ, tmax (fun j => t j + c + η * h j) = tmax (fun j => t j + η * h j) + c :=
    fun h => by
      rw [← tmax_add_const]
      congr 1
      funext j
      ring
  calc ∫ h, tmax (fun j => t j + c + η * h j) * kK h
        = ∫ h, (1 * tmax (fun j => t j + η * h j) + c * 1) * kK h := by
          congr 1
          funext h
          rw [e h]
          ring
    _ = 1 * (∫ h, tmax (fun j => t j + η * h j) * kK h) + c * ∫ h, 1 * kK h :=
          integral_lin_kK (F := fun h => tmax (fun j => t j + η * h j)) (G := fun _ => 1)
            (continuous_tmax_shift η t) continuous_const 1 c
    _ = (∫ h, tmax (fun j => t j + η * h j) * kK h) + c := by
          rw [integral_const_kK]
          ring
end ReciprocityTheory.AnForm.A
