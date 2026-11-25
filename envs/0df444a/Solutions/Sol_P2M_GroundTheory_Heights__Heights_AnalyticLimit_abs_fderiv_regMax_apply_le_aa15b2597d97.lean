-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_fderiv_regMax_apply_le_aa15b2597d97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:10.944336+00:00
-- url     : https://prove2.me/submissions/56fe8fde-f425-4feb-b4c9-ff96b2ab7c41

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
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {η : ℝ} (hη : 0 < η) (p z : ι → ℝ) :
    |fderiv ℝ (regMax (ι := ι) η) p z| ≤ ‖z‖ := by
  classical
  set L := fderiv ℝ (regMax (ι := ι) η) p
  have hz : z = ∑ j, z j • Pi.single j (1 : ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hLz : L z = ∑ j, z j * L (Pi.single j 1) := by
    conv_lhs => rw [hz]
    simp [map_sum, map_smul]
  have hs : ∑ j, L (Pi.single j 1) = 1 := regMax_fderiv_sum hη p
  have hn : ∀ j, 0 ≤ L (Pi.single j 1) := fun j =>
    regMax_fderiv_nonneg hη p _ (Pi.single_nonneg.2 zero_le_one)
  rw [hLz]
  calc |∑ j, z j * L (Pi.single j 1)| ≤ ∑ j, |z j * L (Pi.single j 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |z j| * L (Pi.single j 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hn j)]
    _ ≤ ∑ j, ‖z‖ * L (Pi.single j 1) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (hn j)
        simpa [Real.norm_eq_abs] using norm_le_pi_norm z j
    _ = ‖z‖ := by rw [← Finset.mul_sum, hs, mul_one]
end GroundTheory.Heights₂.Heights.AnalyticLimit
