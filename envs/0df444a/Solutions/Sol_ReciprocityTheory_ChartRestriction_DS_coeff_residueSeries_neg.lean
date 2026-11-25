-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coeff_residueSeries_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:23.073555+00:00
-- url     : https://prove2.me/submissions/85d9d3b9-94ae-4680-873e-da80cc57a8ab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_residueSeries_neg

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
theorem _root_.solution (l : Fin n → ℂ) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries (-l)) = (-1 : ℂ) ^ k * gval l k := by
  rw [residueSeries_neg, map_neg, PowerSeries.coeff_rescale]
  unfold gval
  ring
end ReciprocityTheory.ChartRestriction.DS
