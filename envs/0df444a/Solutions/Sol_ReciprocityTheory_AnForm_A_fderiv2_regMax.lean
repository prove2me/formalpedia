-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv2_regMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:38.853089+00:00
-- url     : https://prove2.me/submissions/5a9e856d-2b11-4ce2-8292-18fe6e51b607

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_one_add_one_le_inf
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hasFDerivAt_comp_smul__eb59e24e54e1
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_regMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_contDiff


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
theorem _root_.solution {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t =
      η⁻¹ • fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • t) := by
  rw [fderiv_regMax hη]
  have hd : DifferentiableAt ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • t) :=
    (regMax_one_contDiff.fderiv_right (m := 1) one_add_one_le_inf).differentiable one_ne_zero _
  exact (hasFDerivAt_comp_smul' η⁻¹ t hd).fderiv
end ReciprocityTheory.AnForm.A
