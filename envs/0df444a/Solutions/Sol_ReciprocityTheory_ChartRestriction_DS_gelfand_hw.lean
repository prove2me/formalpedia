-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gelfand_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:27.30582+00:00
-- url     : https://prove2.me/submissions/18cecbfb-71ea-4e83-b6fc-0405bb8da6b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hwShift_eq_icShift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ePow_hw_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_gx_eq_gval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) : gelfand E k v = gval (icShift (ν + rho n)) k • v := by
  unfold gelfand
  rw [LinearMap.sum_apply]
  simp only [ePow_hw_diag hE hv k, ← Finset.sum_smul, sum_gx_eq_gval, hwShift_eq_icShift]
end ReciprocityTheory.ChartRestriction.DS
