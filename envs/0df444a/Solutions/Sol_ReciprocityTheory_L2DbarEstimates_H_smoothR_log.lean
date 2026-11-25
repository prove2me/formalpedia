-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.smoothR_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:31:56.884825+00:00
-- url     : https://prove2.me/submissions/dcc08cf2-6dc3-409c-8412-91ebe5ea2de2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (f : M → ℝ)
    (hf : SmoothR n z f) (hpos : ∀ x, 0 < f x) : SmoothR n z (fun x => Real.log (f x)) := by
  unfold SmoothR Smooth at *
  intro e he
  have h1 := hf e he
  have h2 : ContDiffOn ℝ ∞ (fun y => f (e.symm y)) e.target := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn h1
    simpa [Function.comp_def] using h
  have h3 : ContDiffOn ℝ ∞ (fun y => Real.log (f (e.symm y))) e.target :=
    h2.log (fun y _ => (hpos _).ne')
  have h4 := Complex.ofRealCLM.contDiff.comp_contDiffOn h3
  simpa [Function.comp_def] using h4
end ReciprocityTheory.L2DbarEstimates.H
