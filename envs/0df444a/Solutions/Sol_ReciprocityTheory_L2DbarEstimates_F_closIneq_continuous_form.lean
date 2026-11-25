-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.closIneq_continuous_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:38.050117+00:00
-- url     : https://prove2.me/submissions/e11f99c8-36e5-461f-aba9-9f431571f8dd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Closure
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] {n : ℕ} (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → V n) (hg : IsTestForm n z g) : Continuous g := by
  have hcoord : ∀ j, Continuous fun x => g x j := by
    intro j
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨e, hxe, hze⟩ := hz x
    have hch : IsChart n z e := fun y _ => congrFun hze y
    have hC := ((hg j).1 e hch).continuousOn
    have h1 : ContinuousAt ((fun x => g x j) ∘ e.symm) (e x) :=
      hC.continuousAt (e.open_target.mem_nhds (e.map_source hxe))
    have h2 : ContinuousAt (((fun x => g x j) ∘ e.symm) ∘ e) x :=
      h1.comp (e.continuousAt hxe)
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hxe] with y hy
    simp [e.left_inv hy]
  have h3 : Continuous fun x => EuclideanSpace.equiv (Fin n) ℂ (g x) :=
    continuous_pi fun j => hcoord j
  have h4 := (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp h3
  convert h4 using 1
  funext x
  exact ((EuclideanSpace.equiv (Fin n) ℂ).symm_apply_apply (g x)).symm
end ReciprocityTheory.L2DbarEstimates.F
