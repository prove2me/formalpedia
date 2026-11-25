-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.aprb_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:24.499359+00:00
-- url     : https://prove2.me/submissions/af71df94-04a8-471b-9f92-e0e9503116d2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) (k : ℕ) : ContDiffOn ℂ k p U := by
  rw [contDiffOn_euclidean]
  intro i
  have h1 : DifferentiableOn ℂ (fun x => p x i) U :=
    (EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp
  exact (contDiffOn_of_differentiableOn n _ U hU h1).of_le (by exact_mod_cast le_top)
end ReciprocityTheory.L2DbarEstimates.Y
