-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.SmoothR.cut_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:42.793538+00:00
-- url     : https://prove2.me/submissions/be504da5-215e-4f60-b526-c3c01586b829

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
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
namespace SmoothR
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  unfold SmoothR Smooth at hf
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hxe, hze⟩ := hz x
  have hch : IsChart n z e := by
    unfold IsChart
    rw [hze]
    exact Set.eqOn_refl _ _
  have hco : ContinuousOn ((fun x => (f x : ℂ)) ∘ e.symm) e.target := (hf e hch).continuousOn
  have h1 : ContinuousAt ((fun x => (f x : ℂ)) ∘ e.symm) (e x) :=
    hco.continuousAt (e.open_target.mem_nhds (e.map_source hxe))
  have h2 : ContinuousAt (((fun x => (f x : ℂ)) ∘ e.symm) ∘ e) x :=
    ContinuousAt.comp (f := e) h1 (e.continuousAt hxe)
  have hev : ((fun x => (f x : ℂ)) ∘ e.symm) ∘ e =ᶠ[𝓝 x] (fun x => (f x : ℂ)) := by
    filter_upwards [e.open_source.mem_nhds hxe] with y hy
    simp [e.left_inv hy]
  have h3 : ContinuousAt (fun x => (f x : ℂ)) x := by
    first
    | exact h2.congr hev
    | exact h2.congr_of_eventuallyEq hev.symm
  have h4 : ContinuousAt (fun y => ((f y : ℂ)).re) x := Complex.continuous_re.continuousAt.comp h3
  simpa using h4
end SmoothR
end ReciprocityTheory.L2DbarEstimates.F
