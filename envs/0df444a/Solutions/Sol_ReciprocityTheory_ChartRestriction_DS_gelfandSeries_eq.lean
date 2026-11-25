-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gelfandSeries_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:51:21.623993+00:00
-- url     : https://prove2.me/submissions/03689292-4e0a-4052-bcaa-79d6f88b8079

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gxSeries_tele

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
theorem _root_.solution (l : Fin n → ℂ) :
    gelfandSeries l = PowerSeries.X * ∑ r, gxSeries l r := by
  have h := gxSeries_tele l n 0 (by simp)
  have e : univ.filter (fun s : Fin n => 0 ≤ s.val) = univ := by ext; simp
  rw [e] at h
  rw [gelfandSeries, ← h]
  ring
end ReciprocityTheory.ChartRestriction.DS
