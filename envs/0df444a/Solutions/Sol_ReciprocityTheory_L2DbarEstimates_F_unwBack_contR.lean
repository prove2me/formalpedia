-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_contR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:58.669722+00:00
-- url     : https://prove2.me/submissions/42788ae2-e983-44b6-951a-b3154cf55d9c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
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
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : SmoothR n z ph) : Continuous ph := by
  unfold SmoothR Smooth at hph
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, hze⟩ := hz x
  have hch : IsChart n z e := fun y _ => by rw [hze]
  have hc : ContinuousAt ((fun y => (ph y : ℂ)) ∘ e.symm) (e x) :=
    ((hph e hch).continuousOn).continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have hc2 : ContinuousAt (((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e) x :=
    hc.comp (e.continuousAt hx)
  have hc3 : ContinuousAt (fun y => (ph y : ℂ)) x := by
    refine hc2.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  exact (Complex.continuous_re.continuousAt.comp hc3).congr
    (Filter.Eventually.of_forall fun y => by simp)
end ReciprocityTheory.L2DbarEstimates.F
