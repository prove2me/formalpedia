-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gval_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:16.334193+00:00
-- url     : https://prove2.me/submissions/ffb90f47-b76c-4558-b821-83af0a06b5ae

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
theorem _root_.solution (l : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) : gval (l ∘ σ) k = gval l k := by
  have h : gelfandSeries (l ∘ σ) = gelfandSeries l := by
    simp only [gelfandSeries, Function.comp_apply]
    rw [Equiv.prod_comp σ (fun r => (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹))]
  rw [gval, gval, h]
end ReciprocityTheory.ChartRestriction.DS
