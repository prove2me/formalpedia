-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.continuous_of_smoothReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:53.230946+00:00
-- url     : https://prove2.me/submissions/752c12dc-0168-4876-b0ae-f32686a0a8e5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_DerivSmoothTransitionOfOneLt
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
    (hz : IsLocalHomeomorph z) (e : M → ℝ) (he : SmoothR n z e) : Continuous e := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨c, hx, hzc⟩ := hz x
  have hc : IsChart n z c := fun y _ => by rw [hzc]
  have hg := (he c hc).continuousOn
  have h1 : ContinuousAt (((fun y => (e y : ℂ)) ∘ c.symm) ∘ c) x :=
    (hg.continuousAt (c.open_target.mem_nhds (c.map_source hx))).comp (c.continuousAt hx)
  have h2 : ((fun y => (e y : ℂ)) ∘ c.symm) ∘ c =ᶠ[𝓝 x] fun y => (e y : ℂ) := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    simp [c.left_inv hy]
  have h3 := Complex.continuous_re.continuousAt.comp (h1.congr h2)
  simpa [Function.comp_def] using h3
end ReciprocityTheory.L2DbarEstimates.F
