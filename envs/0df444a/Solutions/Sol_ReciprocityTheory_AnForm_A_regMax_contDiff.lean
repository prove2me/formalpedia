-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:41.726329+00:00
-- url     : https://prove2.me/submissions/20d0486e-e76b-41aa-8f82-b13076717af9

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_fun

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
theorem _root_.solution {η : ℝ} (hη : 0 < η) : ContDiff ℝ ∞ (regMax (ι := ι) η) := by
  rw [regMax_eq_fun hη]
  exact contDiff_const.mul (regMax_one_contDiff.comp (contDiff_id.const_smul η⁻¹))
end ReciprocityTheory.AnForm.A
