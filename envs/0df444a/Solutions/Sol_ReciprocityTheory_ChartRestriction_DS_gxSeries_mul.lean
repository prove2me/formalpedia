-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gxSeries_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:18.074813+00:00
-- url     : https://prove2.me/submissions/fdd9c357-a2b8-4225-b71f-d655bb4afd3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries

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
    gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
      1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s := by
  ext k
  rcases k with _ | k
  · simp [gxSeries, gx]
  · rw [show gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
        gxSeries l r - PowerSeries.C (l r) * (gxSeries l r * PowerSeries.X) by ring,
      map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, map_sub,
      PowerSeries.coeff_succ_X_mul, map_sum]
    simp [gxSeries, gx, PowerSeries.coeff_one]
end ReciprocityTheory.ChartRestriction.DS
