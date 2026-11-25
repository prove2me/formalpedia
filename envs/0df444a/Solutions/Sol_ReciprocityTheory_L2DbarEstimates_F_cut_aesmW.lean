-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_aesmW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:27:16.395558+00:00
-- url     : https://prove2.me/submissions/8b6a79ed-d0d8-4758-adea-569d50fe9248

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub

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
private lemma continuous_coord_apply {n : ℕ} (j : Fin n) : Continuous (fun v : V n => v j) := by
  first
  | fun_prop
  | continuity
  | exact (EuclideanSpace.proj j).continuous
  | exact continuous_apply j
end
end ReciprocityTheory.L2DbarEstimates.F
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (z : M → V n) (μ : Measure M) (ph ψ η c : M → ℝ) (f : M → V n) (w : M → ℂ)
    (hc : Continuous c) (hE : Continuous (fun x => w1 ph ψ x - w2 ph ψ x))
    (hd : ∀ j, Continuous (d n z j (fun y => (η y : ℂ))))
    (hf : AEStronglyMeasurable f μ) (hw : AEStronglyMeasurable w μ) :
    AEStronglyMeasurable (fun x => (c x : ℂ) * w x - (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ) *
      ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j) μ := by
  have h1 : AEStronglyMeasurable (fun x => (c x : ℂ) * w x) μ :=
    (Complex.continuous_ofReal.comp hc).aestronglyMeasurable.mul hw
  have h2 : AEStronglyMeasurable (fun x => (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hE)).aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun x => ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j) μ := by
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin n)), AEStronglyMeasurable
        (fun x => d n z j (fun y => (η y : ℂ)) x * f x j) μ := fun j _ =>
      (hd j).aestronglyMeasurable.mul ((continuous_coord_apply j).comp_aestronglyMeasurable hf)
    first
    | exact Finset.aestronglyMeasurable_sum' _ hj
    | exact Finset.aestronglyMeasurable_fun_sum _ hj
    | exact (Finset.aestronglyMeasurable_sum _ hj).congr (ae_of_all _ fun x => by simp)
  exact h1.sub (h2.mul h3)
end ReciprocityTheory.L2DbarEstimates.F
