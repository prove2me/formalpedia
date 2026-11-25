-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.smoothR_vsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:50:16.448147+00:00
-- url     : https://prove2.me/submissions/d2146326-1437-46d9-87b8-7b34dd2cb4bc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth


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
theorem _root_.solution (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) {p : ℕ}
    (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l)) : SmoothR n z (fun x => vsq (gv g x)) := by
  unfold SmoothR Smooth
  intro e he
  have hd : ∀ l, ContDiffOn ℝ ∞ (fun y => g l (e.symm y)) e.target := by
    intro l
    have h1 : ContDiffOn ℝ ∞ (g l ∘ e.symm) e.target := Holo.smooth n z (g l) (hg l) e he
    exact h1
  have hs : ContDiffOn ℝ ∞ (fun y => ∑ l, ‖g l (e.symm y)‖ ^ 2) e.target :=
    ContDiffOn.sum (fun l _ => (contDiff_norm_sq ℂ).comp_contDiffOn (hd l))
  have h4 := Complex.ofRealCLM.contDiff.comp_contDiffOn hs
  simpa [Function.comp_def, vsq, gv] using h4
end ReciprocityTheory.L2DbarEstimates.H
