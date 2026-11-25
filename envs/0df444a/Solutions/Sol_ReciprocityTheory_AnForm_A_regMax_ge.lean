-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:32.609084+00:00
-- url     : https://prove2.me/submissions/af418e5a-d568-4da6-9973-f5e0ca3f5c7d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_affine_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax_shift
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_kK_mono

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
theorem _root_.solution (η : ℝ) (t : ι → ℝ) : tmax t ≤ regMax η t := by
  obtain ⟨i, hi⟩ := exists_tmax t
  rw [regMax_eq_kK]
  calc tmax t = t i := hi
    _ = ∫ h, (t i + η * h i) * kK h := (integral_affine_kK (t i) η i).symm
    _ ≤ ∫ h, tmax (fun j => t j + η * h j) * kK h :=
        integral_kK_mono (F := fun h => t i + η * h i) (G := fun h => tmax (fun j => t j + η * h j))
          (continuous_const.add (continuous_const.mul (continuous_apply i)))
          (continuous_tmax_shift η t) fun h _ => le_tmax (fun j => t j + η * h j) i
end ReciprocityTheory.AnForm.A
