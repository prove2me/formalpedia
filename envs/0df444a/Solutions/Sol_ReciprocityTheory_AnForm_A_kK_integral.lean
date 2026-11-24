-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.kK_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:44.380841+00:00
-- url     : https://prove2.me/submissions/55ed36fe-b878-48f5-9a91-e3ff85f7760b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__integral_37214bfa7034

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
theorem _root_.solution : ∫ h : ι → ℝ, kK h = 1 := by
  show ∫ h : ι → ℝ, ∏ j, kθ (h j) = 1
  first
    | rw [integral_fintype_prod_eq_pow ι kθ, kθ_integral, one_pow]
    | rw [integral_fintype_prod_eq_prod ι (fun _ => kθ)]; simp [kθ_integral]
    | (rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (fun _ => kθ)]; simp [kθ_integral])
end ReciprocityTheory.AnForm.A
