-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_aesmS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:27:53.849965+00:00
-- url     : https://prove2.me/submissions/15edd939-b876-4b6e-b64d-c2a9f1205578

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
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
    (n : ℕ) (z : M → V n) (μ : Measure M) (η c : M → ℝ) (f : M → V n)
    (σ : M → Fin n → Fin n → ℂ) (hc : Continuous c)
    (hd : ∀ j, Continuous (db n z j (fun y => (η y : ℂ))))
    (hf : AEStronglyMeasurable f μ) (hσ : AEStronglyMeasurable σ μ) :
    AEStronglyMeasurable (fun x => fun j k => (c x : ℂ) * σ x j k +
      wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i) j k) μ := by
  have ha : Continuous (fun x => fun i => db n z i (fun y => (η y : ℂ)) x) :=
    continuous_pi fun i => hd i
  have hb : AEStronglyMeasurable (fun x => fun i => f x i) μ :=
    (continuous_pi fun i => continuous_coord_apply (n := n) i).comp_aestronglyMeasurable hf
  have hW : Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => wedge p.1 p.2) := by
    show Continuous fun p : (Fin n → ℂ) × (Fin n → ℂ) => fun j k => p.1 j * p.2 k - p.1 k * p.2 j
    first
    | fun_prop
    | exact continuous_pi fun j => continuous_pi fun k =>
        (((continuous_apply j).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)).sub
          (((continuous_apply k).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))
  have hpair : AEStronglyMeasurable
      (fun x => ((fun i => db n z i (fun y => (η y : ℂ)) x), (fun i => f x i))) μ := by
    first
    | exact ha.aestronglyMeasurable.prodMk hb
    | exact ha.aestronglyMeasurable.prod_mk hb
  have h2 : AEStronglyMeasurable
      (fun x => wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i)) μ :=
    hW.comp_aestronglyMeasurable hpair
  have h1 : AEStronglyMeasurable (fun x => (c x : ℂ) • σ x) μ :=
    (Complex.continuous_ofReal.comp hc).aestronglyMeasurable.smul hσ
  first
  | exact h1.add h2
  | exact (h1.add h2).congr (ae_of_all _ fun x => by funext j k; simp)
end ReciprocityTheory.L2DbarEstimates.F
