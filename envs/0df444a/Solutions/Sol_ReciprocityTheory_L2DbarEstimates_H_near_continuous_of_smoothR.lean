-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.near_continuous_of_smoothR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:50.893082+00:00
-- url     : https://prove2.me/submissions/11f86e55-d8da-4b51-9c5a-aa2c5a1c962c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


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
open scoped ENNReal InnerProductSpace
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hc : Continuous (fun x => (f x : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e, hx, he⟩ := hz x
    have hch : IsChart n z e := fun y _ => by rw [he]
    have h1 := (hf e hch).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
    have h2 : ContinuousAt (((fun y => (f y : ℂ)) ∘ e.symm) ∘ e) x :=
      ContinuousAt.comp (f := e) h1 (e.continuousAt hx)
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  exact (Complex.continuous_re.comp hc).congr fun x => by simp
end ReciprocityTheory.L2DbarEstimates.H
