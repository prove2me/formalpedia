-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.locL2_form_component
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:47.446833+00:00
-- url     : https://prove2.me/submissions/e8c7a197-6f19-432d-b541-9d35c9aa9cdf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
private lemma localL2Isometry_comp_of_norm_le {M E F : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (μ : Measure M) (f : M → E) (g : E → F)
    (hg : Continuous g) (hb : ∀ e, ‖g e‖ ≤ ‖e‖) (hf : LocalL2Isometry μ f) :
    LocalL2Isometry μ (fun x => g (f x)) := by
  unfold LocalL2Isometry at hf ⊢
  refine ⟨hg.comp_aestronglyMeasurable hf.1, fun C hC => lt_of_le_of_lt ?_ (hf.2 C hC)⟩
  refine lintegral_mono fun x => ?_
  gcongr
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (hb _)
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) (f : M → V n) (hf : LocalL2Isometry μ f) (j : Fin n) :
    LocalL2Isometry μ (fun x => f x j) := by
  refine localL2Isometry_comp_of_norm_le μ f (fun v : V n => v j) (EuclideanSpace.proj (𝕜 := ℂ) j).continuous ?_ hf
  intro v
  rw [EuclideanSpace.norm_eq]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)))
end ReciprocityTheory.L2DbarEstimates.F
