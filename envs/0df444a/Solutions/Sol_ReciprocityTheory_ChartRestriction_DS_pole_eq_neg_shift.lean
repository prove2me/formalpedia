-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.pole_eq_neg_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:00.865679+00:00
-- url     : https://prove2.me/submissions/b51e46be-5ae0-468d-8aa0-211c8e61e4a2

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
theorem _root_.solution (μ : Fin n → ℝ) : poleV μ = -icShift (-μ) := by
  funext s
  simp only [poleV, icShift, Pi.neg_apply]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.DS
