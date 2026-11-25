-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fderiv_isBigO_of_isBigO_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:26:13.210654+00:00
-- url     : https://prove2.me/submissions/5850c788-bf8f-46c5-9f42-0a7c3f9cc6db

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Lemmata_CharacterDirections_Cdir
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Theorems.Thm_Bl_CoprimeDirections_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) {m : ℕ}
    (hO : f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1 + 1)) :
    fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by
  first | exact Bl.CoprimeDirections.goal1 .. | (apply Bl.CoprimeDirections.goal1 <;> assumption) | (intros; apply Bl.CoprimeDirections.goal1 <;> assumption)
end ReciprocityTheory.L2DbarEstimates.Y
