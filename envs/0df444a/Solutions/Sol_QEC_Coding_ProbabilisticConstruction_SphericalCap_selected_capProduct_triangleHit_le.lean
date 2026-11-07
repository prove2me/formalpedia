-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.selected_capProduct_triangleHit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:54.144681+00:00
-- url     : https://prove2.me/submissions/1f9e41a8-ea1b-4fe9-9c89-db5c8822fb00

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capProduct_triangleHit_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_selected_product_measurePreserving
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_isProbabilityMeasure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_triangleHit


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {ι : Type*} [Fintype ι]
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : ι → Sphere) (c : ι → ℝ) (hc0 : ∀ i, -1 < c i) (hc1 : ∀ i, c i < 1)
    (j : Fin 3 → ι) (hj : Function.Injective j) (r : Fin 3 → Space) (z : Space) :
    Measure.pi (fun k => capDisplacementLaw R (u k) (c k))
      {p | (fun k => p (j k)) ∈ triangleHit r z ρ} ≤
      ENNReal.ofReal ((6*ρ/R) * ∑ k, 1/(1-c (j k))) := by
  letI (k : ι) : IsProbabilityMeasure (capDisplacementLaw R (u k) (c k)) :=
    capDisplacementLaw_isProbabilityMeasure R (u k) (hc1 k)
  have hp := selected_product_measurePreserving
    (fun k => capDisplacementLaw R (u k) (c k)) j hj
  change Measure.pi (fun k => capDisplacementLaw R (u k) (c k))
    ((fun p : ι → Space => fun k => p (j k)) ⁻¹' triangleHit r z ρ) ≤ _
  rw [hp.measure_preimage (measurableSet_triangleHit r z ρ).nullMeasurableSet]
  exact capProduct_triangleHit_le hR hρ (fun k => u (j k)) (fun k => c (j k))
    (fun k => hc0 (j k)) (fun k => hc1 (j k)) r z
end QEC.Coding.ProbabilisticConstruction.SphericalCap
