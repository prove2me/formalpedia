-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.contDiff_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:13.218508+00:00
-- url     : https://prove2.me/submissions/e67fd9dc-ba1b-4518-9451-3cadd51ba0e0

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
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : X → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, ContDiff ℂ ∞ (fun x => f x i j)) : ContDiff ℂ ∞ f := by
  exact contDiff_pi.2 fun i => contDiff_pi.2 fun j => h i j
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
