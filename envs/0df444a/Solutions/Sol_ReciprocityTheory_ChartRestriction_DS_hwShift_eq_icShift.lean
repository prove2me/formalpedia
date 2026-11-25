-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.hwShift_eq_icShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:20.367584+00:00
-- url     : https://prove2.me/submissions/0c254936-9c2a-4b59-8de7-c3b1fd4f37bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW

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
theorem _root_.solution (ν : Fin n → ℝ) : hwShift ν = icShift (ν + rho n) := by
  funext r
  have hr := r.isLt
  simp only [hwShift, icShift, rho, Pi.add_apply]
  rw [Nat.cast_sub (by omega : (r : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.DS
