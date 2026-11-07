-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.selected_product_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:40:50.663172+00:00
-- url     : https://prove2.me/submissions/91ed1b04-a64c-4bfe-8bc8-4463098f4e21

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {ι : Type*} [Fintype ι]
    (μ : ι → Measure Space) [∀ i, IsProbabilityMeasure (μ i)]
    (j : Fin 3 → ι) (hj : Function.Injective j) :
    MeasurePreserving (fun p : ι → Space => fun k => p (j k))
      (Measure.pi μ) (Measure.pi fun k => μ (j k)) := by
  have hind : iIndepFun (fun i (p : ι → Space) => p i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨by fun_prop, ?_⟩
  have he := iIndepFun.map_fun_eq_pi_map (fun k => (measurable_pi_apply (j k)).aemeasurable) (hind.precomp hj)
  simpa only [(measurePreserving_eval μ _).map_eq] using he
end QEC.Coding.ProbabilisticConstruction.SphericalCap
