-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.isOpen_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:40.474673+00:00
-- url     : https://prove2.me/submissions/0f17c6f1-5cca-4832-8d6b-550a4147bb6a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isOpen_omega


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
theorem _root_.solution : IsOpen (OmegaSet n : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  exact ReciprocityTheory.ChartRestriction.DS.S7.isOpen_omega
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
