-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_mem_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:17.175083+00:00
-- url     : https://prove2.me/submissions/43238786-df17-42f5-97d8-e36dbca8b858

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
theorem _root_.solution {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) : circleMap 0 ρ θ ∈ closedBall (0 : ℂ) ρ := circleMap_mem_closedBall 0 hρ.le θ
end ReciprocityTheory.ChartRestriction.DS.S7
