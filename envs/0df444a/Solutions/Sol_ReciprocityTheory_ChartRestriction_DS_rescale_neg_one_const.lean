-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rescale_neg_one_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:22.068452+00:00
-- url     : https://prove2.me/submissions/f6d9e824-2594-4b94-a5d1-050729c03657

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent

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
    PowerSeries.rescale (-1 : ℂ) (PowerSeries.C c) = PowerSeries.C c := by
  ext m
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · simp [h]
  · simp
end ReciprocityTheory.ChartRestriction.DS
