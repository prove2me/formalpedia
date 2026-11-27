-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.CkR.differentiableAt_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:50.700205+00:00
-- url     : https://prove2.me/submissions/7d323fd8-97fe-4a5b-a27f-8a7a26e0bad6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_Ck_differentiableAt_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
namespace CkR
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (ph : M → ℝ) (hph : CkR n z 1 ph) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (x : M) (hx : x ∈ e.source) :
    DifferentiableAt ℝ (fun w => ph (e.symm w)) (z x) := by
  have h := (Complex.reCLM.differentiable.differentiableAt).comp (z x)
    (Ck.differentiableAt_chart n z _ hph e he x hx)
  have e1 : (fun w => ph (e.symm w)) = ⇑Complex.reCLM ∘ (fun x => (ph x : ℂ)) ∘ e.symm := by
    funext w; simp
  rw [e1]
  exact h
end CkR
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
