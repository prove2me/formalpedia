-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capProduct_largeWeightHit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:48:08.843619+00:00
-- url     : https://prove2.me/submissions/c732bf90-14f9-48aa-a02b-56662bb0919b

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_pi_event_le_of_sections
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_largeWeightHit_section_subset_slab
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_isProbabilityMeasure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_slab_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_isClosed_largeWeightHit


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : Fin 3 → Sphere) (c : Fin 3 → ℝ) (hc0 : ∀ i, -1 < c i) (hc1 : ∀ i, c i < 1)
    (r : Fin 3 → Space) (z : Space) (i : Fin 3) :
    Measure.pi (fun j => capDisplacementLaw R (u j) (c j)) (largeWeightHit r z ρ i) ≤
      ENNReal.ofReal (6*ρ/(R*(1-c i))) := by
  letI (j : Fin 3) : IsProbabilityMeasure (capDisplacementLaw R (u j) (c j)) :=
    capDisplacementLaw_isProbabilityMeasure R (u j) (hc1 j)
  apply pi_event_le_of_sections _ i (isClosed_largeWeightHit r z ρ i).measurableSet
  intro q
  obtain ⟨n,hn⟩ := largeWeightHit_section_subset_slab r z ρ i q
  have hb := capDisplacementLaw_slab_le hR (u i) n (hc0 i) (hc1 i)
    (inner ℝ (n : Space) (z-r i)) (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hρ)
  have he : 2*(3*ρ)/(R*(1-c i)) = 6*ρ/(R*(1-c i)) := by ring
  rw [he] at hb
  exact (measure_mono hn).trans hb
end QEC.Coding.ProbabilisticConstruction.SphericalCap
