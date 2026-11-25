-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.oneSubCX_const_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:40.380281+00:00
-- url     : https://prove2.me/submissions/8a8e628e-9c0d-476c-9675-307a0829fbed

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
theorem _root_.solution (a : ℂ) : PowerSeries.constantCoeff (1 - PowerSeries.C a * PowerSeries.X) ≠ 0 := by
  simp
end ReciprocityTheory.ChartRestriction.DS
