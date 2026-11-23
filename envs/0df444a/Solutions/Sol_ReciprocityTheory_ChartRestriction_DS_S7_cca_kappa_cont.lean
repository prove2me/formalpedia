-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_kappa_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:58.685817+00:00
-- url     : https://prove2.me/submissions/2c68f8b2-9b8c-44e9-92f7-5378218cb1c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ρ : ℝ} (hρ : 0 < ρ) : Continuous (ccaKappa ρ) := by
  show Continuous fun θ => ccaKappa ρ θ
  simp only [ccaKappa, deriv_circleMap, sub_zero]
  refine ((continuous_circleMap 0 ρ).mul continuous_const).mul ?_
  refine continuous_const.div ((continuous_circleMap 0 ρ).pow 2) (fun θ => ?_)
  exact pow_ne_zero 2 (circleMap_ne_center hρ.ne')
end ReciprocityTheory.ChartRestriction.DS.S7
