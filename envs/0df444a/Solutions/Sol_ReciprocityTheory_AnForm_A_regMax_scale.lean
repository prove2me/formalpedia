-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:10.040571+00:00
-- url     : https://prove2.me/submissions/b8ecc8c6-830e-43cd-ad5f-81f63f912f62

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_scale

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
theorem _root_.solution {η : ℝ} (hη : 0 < η) (t : ι → ℝ) : regMax η t = η * regMax 1 (η⁻¹ • t) := by
  rw [regMax_eq_kK, regMax_eq_kK]
  first
    | rw [← integral_const_mul]
    | rw [← integral_mul_left]
  congr 1
  funext h
  rw [tmax_scale hη t h, mul_assoc]
end ReciprocityTheory.AnForm.A
