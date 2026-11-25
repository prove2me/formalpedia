-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.sm_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:09.700098+00:00
-- url     : https://prove2.me/submissions/ce1bf2a2-3677-4a1f-a4e7-c6aba11217d2

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
theorem _root_.solution (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) := by
  exact phiM_contDiffOn μ
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
