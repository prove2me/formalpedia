-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv_regMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:30.724148+00:00
-- url     : https://prove2.me/submissions/a8661c12-136c-4c88-b1de-f38e44190c2d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hasFDerivAt_comp_smul__eb59e24e54e1
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_fun
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
theorem _root_.solution {η : ℝ} (hη : 0 < η) :
    fderiv ℝ (regMax (ι := ι) η) = fun t => fderiv ℝ (regMax (ι := ι) 1) (η⁻¹ • t) := by
  funext t
  rw [regMax_eq_fun hη]
  have hd : DifferentiableAt ℝ (regMax (ι := ι) 1) (η⁻¹ • t) :=
    regMax_one_contDiff.differentiable (by simp) _
  rw [((hasFDerivAt_comp_smul' η⁻¹ t hd).const_mul η).fderiv, smul_smul,
    mul_inv_cancel₀ hη.ne', one_smul]
end ReciprocityTheory.AnForm.A
