-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:37.404897+00:00
-- url     : https://prove2.me/submissions/5b9f0c17-feca-4974-a204-a62b7136cb11

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_mul_coord_bounds
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax_shift
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_kK_mono
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_const_kK

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
theorem _root_.solution {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ) : regMax η t ≤ tmax t + η / 2 := by
  rw [regMax_eq_kK]
  calc ∫ h, tmax (fun j => t j + η * h j) * kK h ≤ ∫ h, (tmax t + η / 2) * kK h :=
        integral_kK_mono (F := fun h => tmax (fun j => t j + η * h j)) (G := fun _ => tmax t + η / 2)
          (continuous_tmax_shift η t) continuous_const fun h hh =>
          tmax_le fun j => by
            show t j + η * h j ≤ tmax t + η / 2
            linarith [(mul_coord_bounds hη hh j).2, le_tmax t j]
    _ = tmax t + η / 2 := integral_const_kK _
end ReciprocityTheory.AnForm.A
