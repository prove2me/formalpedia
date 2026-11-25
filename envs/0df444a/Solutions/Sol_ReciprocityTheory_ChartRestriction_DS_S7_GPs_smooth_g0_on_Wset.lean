-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.smooth_g0_on_Wset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:09.491646+00:00
-- url     : https://prove2.me/submissions/d24a2325-47d7-4b08-94ec-e4866568b0e6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_trip
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_sm_phi

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
theorem _root_.solution (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (g0 μ) (Wset n) := by
  exact (sm_phi μ).comp contDiff_trip.contDiffOn (fun p hp => hp)
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
