-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sum_gx_eq_gval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:47.253662+00:00
-- url     : https://prove2.me/submissions/69fee3b8-d04e-4307-bc28-0aca45edd73e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gelfandSeries_eq

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
theorem _root_.solution (l : Fin n → ℂ) (k : ℕ) : ∑ r, gx l k r = gval l k := by
  rw [gval, gelfandSeries_eq, PowerSeries.coeff_succ_X_mul, map_sum]
  simp [gxSeries]
end ReciprocityTheory.ChartRestriction.DS
