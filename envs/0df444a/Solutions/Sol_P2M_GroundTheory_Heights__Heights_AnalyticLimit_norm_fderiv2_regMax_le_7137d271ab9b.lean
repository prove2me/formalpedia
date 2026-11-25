-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_fderiv2_regMax_le_7137d271ab9b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:41:30.858956+00:00
-- url     : https://prove2.me/submissions/e36c322d-374d-407f-9090-56fc8f5e3351

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_two_le_inf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution : ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ p : ι → ℝ,
    ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p‖ ≤ C / η := by
  obtain ⟨C, hC⟩ := regMax_one_fderiv2_bound (ι := ι)
  refine ⟨C, fun η hη p => ?_⟩
  rw [fderiv2_regMax hη]
  calc ‖η⁻¹ • fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • p)‖
      ≤ ‖η⁻¹‖ * ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • p)‖ :=
        ContinuousLinearMap.opNorm_smul_le η⁻¹ (fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • p))
    _ = η⁻¹ * ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • p)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
    _ ≤ η⁻¹ * C := mul_le_mul_of_nonneg_left (hC _) (inv_pos.2 hη).le
    _ = C / η := by ring
end GroundTheory.Heights₂.Heights.AnalyticLimit
