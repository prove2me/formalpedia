-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_fderiv2_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:58.022305+00:00
-- url     : https://prove2.me/submissions/1f939711-6d23-4963-bbd2-9cc8f56af5c9

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax

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
theorem _root_.solution : ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ (t v w : ι → ℝ), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
    |fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t v w| ≤ C / η := by
  obtain ⟨C, hC⟩ := regMax_one_fderiv2_bound (ι := ι)
  refine ⟨C, fun η hη t v w hv hw => ?_⟩
  rw [fderiv2_regMax hη, ← Real.norm_eq_abs]
  set A := fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • t)
  have hA : ‖A v w‖ ≤ C :=
    calc ‖A v w‖ ≤ ‖A‖ * ‖v‖ * ‖w‖ := A.le_opNorm₂ v w
      _ ≤ ‖A‖ * 1 * 1 := by gcongr
      _ ≤ C := by simpa using hC (η⁻¹ • t)
  rw [smul_apply, smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hA (inv_pos.2 hη).le
end ReciprocityTheory.AnForm.A
