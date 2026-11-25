-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.contDiff_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:49.262549+00:00
-- url     : https://prove2.me/submissions/dff642f6-e193-44c4-8ea3-7dac04fdd7a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (i j : Fin n) : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z i j) := by
  first
    | exact contDiff_apply_apply (𝕜 := ℂ) (n := ∞) i j
    | fun_prop
    | exact ((contDiff_apply ℂ (Fin n → ℂ) i).clm_apply contDiff_const).comp contDiff_id
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
