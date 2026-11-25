-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.residueSeries_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:45.663573+00:00
-- url     : https://prove2.me/submissions/40b24aec-ba3a-4b61-bd30-a3067c9b220a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rescale_neg_one_geometric_inv

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
theorem _root_.solution (l : Fin n → ℂ) :
    resSeries (-l) = -PowerSeries.rescale (-1 : ℂ) (gelfandSeries l) := by
  have key : ∀ s, (1 + PowerSeries.X * (1 - PowerSeries.C ((-l) s) * PowerSeries.X)⁻¹) =
      PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by
    intro s
    rw [map_sub, map_one, map_mul, PowerSeries.rescale_X, rescale_neg_one_geometric_inv]
    simp only [Pi.neg_apply, map_neg, map_one, neg_mul, one_mul, sub_neg_eq_add]
  unfold resSeries gelfandSeries
  simp_rw [key]
  rw [← map_prod, map_sub, map_one]
  ring
end ReciprocityTheory.ChartRestriction.DS
