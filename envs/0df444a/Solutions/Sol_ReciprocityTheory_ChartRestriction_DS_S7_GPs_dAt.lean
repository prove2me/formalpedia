-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.dAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:52.876543+00:00
-- url     : https://prove2.me/submissions/634f7f02-03a2-4d35-90d0-87e3b6e7f7a1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) {g : Matrix (Fin n) (Fin n) ℂ → E}
    (hg : ContDiffOn ℂ ∞ g V) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ V) : DifferentiableAt ℂ g z := by
  exact (hg.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
