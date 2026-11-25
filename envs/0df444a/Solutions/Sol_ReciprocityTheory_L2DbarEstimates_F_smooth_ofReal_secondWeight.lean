-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.smooth_ofReal_secondWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:28.183085+00:00
-- url     : https://prove2.me/submissions/0fe6f684-4520-4d92-9285-98838972696c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ψ : M → ℝ)
    (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    Smooth n z (fun y => ((w2 ph ψ y : ℝ) : ℂ)) := by
  unfold SmoothR at hph hψ
  unfold Smooth at hph hψ ⊢
  intro e he
  refine ((hph e he).sub (hψ e he)).congr fun p _ => ?_
  simp [w2]
end ReciprocityTheory.L2DbarEstimates.F
