-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.multA_contR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:56.123809+00:00
-- url     : https://prove2.me/submissions/78048dd6-2ebf-429c-bf3c-f10ec9aa0e7e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
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
theorem _root_.solution {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : SmoothR n z ph) : Continuous ph := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, hze⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [hze]
  have hg := (hph e hc).continuousOn
  have h1 : ContinuousAt (((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e) x :=
    (hg.continuousAt (e.open_target.mem_nhds (e.map_source hx))).comp (e.continuousAt hx)
  have h2 : ((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e =ᶠ[𝓝 x] fun y => (ph y : ℂ) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  have h3 := Complex.continuous_re.continuousAt.comp (h1.congr h2)
  simpa [Function.comp_def] using h3
end ReciprocityTheory.L2DbarEstimates.F
