-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.smoothR_secondWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:20.008015+00:00
-- url     : https://prove2.me/submissions/7fa52bd6-b03d-44e1-b024-d01863c3e627

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (ph ψ : M → ℝ) (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    SmoothR n z (w2 ph ψ) := by
  unfold SmoothR Smooth at *
  intro e he
  refine ((hph e he).sub (hψ e he)).congr fun y _ => ?_
  simp [w2]
end ReciprocityTheory.L2DbarEstimates.F
