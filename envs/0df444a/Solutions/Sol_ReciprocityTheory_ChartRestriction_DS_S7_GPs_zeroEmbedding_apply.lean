-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.zeroEmbedding_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:43.334749+00:00
-- url     : https://prove2.me/submissions/7e4bb7d3-5ad2-419d-b913-a6f48e5d3a7d

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
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) : I0 n H = (H, 0) := by
  have hs : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => ((y, 0) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
      ((ContinuousLinearMap.id ℂ _).prod 0) 0 := (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  unfold I0
  rw [hs.fderiv]
  rfl
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
