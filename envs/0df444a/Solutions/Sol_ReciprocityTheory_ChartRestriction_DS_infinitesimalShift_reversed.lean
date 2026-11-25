-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.infinitesimalShift_reversed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:31.073902+00:00
-- url     : https://prove2.me/submissions/2f61149c-8b55-4f5a-9b53-50c48e560374

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
theorem _root_.solution (ν : Fin n → ℝ) :
    icShift ((fun r => -ν (Fin.rev r)) + rho n) = icShift (-(ν + rho n)) ∘ Fin.revPerm := by
  funext r
  have hr : (r : ℕ) + 1 ≤ n := r.2
  simp only [icShift, Function.comp_apply, Pi.add_apply, Pi.neg_apply, rho, Fin.revPerm_apply, Fin.val_rev]
  push_cast [Nat.cast_sub hr]
  ring
end ReciprocityTheory.ChartRestriction.DS
