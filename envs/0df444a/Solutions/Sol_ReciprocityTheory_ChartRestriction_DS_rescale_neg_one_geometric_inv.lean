-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rescale_neg_one_geometric_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:16.401953+00:00
-- url     : https://prove2.me/submissions/be4124e7-0925-40a1-aaf1-a071ea316aa6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rescale_neg_one_const

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
theorem _root_.solution (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) ((1 - PowerSeries.C c * PowerSeries.X)⁻¹) =
      (1 + PowerSeries.C c * PowerSeries.X)⁻¹ := by
  have h1 : PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.C c * PowerSeries.X) =
      1 + PowerSeries.C c * PowerSeries.X := by
    simp [PowerSeries.rescale_X, rescale_neg_one_const]
  have hc0 : PowerSeries.constantCoeff (1 - PowerSeries.C c * PowerSeries.X) ≠ 0 := by simp
  have hc1 : PowerSeries.constantCoeff (1 + PowerSeries.C c * PowerSeries.X) ≠ 0 := by simp
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc1, ← h1, ← map_mul, PowerSeries.inv_mul_cancel _ hc0, map_one]
end ReciprocityTheory.ChartRestriction.DS
