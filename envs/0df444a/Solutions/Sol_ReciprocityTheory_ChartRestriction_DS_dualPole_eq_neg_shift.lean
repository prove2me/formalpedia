-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dualPole_eq_neg_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:25.174873+00:00
-- url     : https://prove2.me/submissions/9e40db55-2998-4386-b2fc-21c4b4b9e788

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
theorem _root_.solution (μ : Fin n → ℝ) : poleVd μ = -icShift μ := by
  funext s
  simp only [poleVd, icShift, Pi.neg_apply]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.DS
