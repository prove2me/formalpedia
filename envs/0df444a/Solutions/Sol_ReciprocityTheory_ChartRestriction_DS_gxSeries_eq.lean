-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gxSeries_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:52.682118+00:00
-- url     : https://prove2.me/submissions/209e7b01-0d85-4b91-a6e6-69278a489f76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gxSeries_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_oneSubCX_const_ne

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (l : Fin n → ℂ) (r : Fin n) :
    gxSeries l r = (1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s) *
      (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹ := by
  rw [← gxSeries_mul, mul_assoc, PowerSeries.mul_inv_cancel _ (oneSubCX_const_ne _), mul_one]
end ReciprocityTheory.ChartRestriction.DS
