-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.norm_le_of_kK_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:15.228864+00:00
-- url     : https://prove2.me/submissions/192e9ebe-62c2-4655-a0ed-186012618b58

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98

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
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {h : ι → ℝ} (hh : kK h ≠ 0) : ‖h‖ ≤ 1 / 2 := by
  have hh' : ∏ j, kθ (h j) ≠ 0 := hh
  have hj : ∀ j, kθ (h j) ≠ 0 := fun j => (Finset.prod_ne_zero_iff.1 hh') j (Finset.mem_univ j)
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact abs_le_of_kθ_ne (hj j)
end ReciprocityTheory.AnForm.A
