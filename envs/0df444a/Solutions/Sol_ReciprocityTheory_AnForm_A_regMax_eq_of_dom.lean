-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_eq_of_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:40.375473+00:00
-- url     : https://prove2.me/submissions/c1135d53-be13-4fbe-b987-2e22a49b0dc8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_eq_of_forall_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_affine_kK
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
theorem _root_.solution {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ) (i : ι)
    (hi : ∀ j, j ≠ i → t j + η ≤ t i) : regMax η t = t i := by
  rw [regMax_eq_kK]
  calc ∫ h, tmax (fun j => t j + η * h j) * kK h = ∫ h, (t i + η * h i) * kK h :=
        integral_kK_congr (F := fun h => tmax (fun j => t j + η * h j)) (G := fun h => t i + η * h i)
          fun h hh => by
            show tmax (fun j => t j + η * h j) = t i + η * h i
            apply tmax_eq_of_forall_le (i := i)
            intro j
            show t j + η * h j ≤ t i + η * h i
            by_cases hj : j = i
            · rw [hj]
            · linarith [hi j hj, (mul_coord_bounds hη hh j).2, (mul_coord_bounds hη hh i).1]
    _ = t i := integral_affine_kK _ _ _
end ReciprocityTheory.AnForm.A
