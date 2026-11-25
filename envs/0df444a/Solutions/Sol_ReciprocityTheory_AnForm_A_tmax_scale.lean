-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tmax_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:37.95914+00:00
-- url     : https://prove2.me/submissions/3f142702-1b4b-4092-8d64-2ab9fabdb172

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_smul

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
theorem _root_.solution {η : ℝ} (hη : 0 < η) (t h : ι → ℝ) :
    tmax (fun j => t j + η * h j) = η * tmax (fun j => (η⁻¹ • t) j + 1 * h j) := by
  rw [← tmax_smul _ hη.le]
  congr 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_add, ← mul_assoc η η⁻¹, mul_inv_cancel₀ hη.ne']
  ring
end ReciprocityTheory.AnForm.A
