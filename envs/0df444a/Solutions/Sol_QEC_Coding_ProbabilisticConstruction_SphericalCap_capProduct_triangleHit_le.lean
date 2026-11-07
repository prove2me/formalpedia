-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capProduct_triangleHit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:49:22.790327+00:00
-- url     : https://prove2.me/submissions/d82976f9-a082-4044-bc7c-533c3a6df444

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capProduct_largeWeightHit_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_triangleHit_eq_union


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : Fin 3 → Sphere) (c : Fin 3 → ℝ) (hc0 : ∀ i, -1 < c i) (hc1 : ∀ i, c i < 1)
    (r : Fin 3 → Space) (z : Space) :
    Measure.pi (fun j => capDisplacementLaw R (u j) (c j)) (triangleHit r z ρ) ≤
      ENNReal.ofReal ((6*ρ/R) * ∑ i, 1/(1-c i)) := by
  rw [triangleHit_eq_union]
  calc
    _ ≤ ∑ i, Measure.pi (fun j => capDisplacementLaw R (u j) (c j))
        (largeWeightHit r z ρ i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (6*ρ/(R*(1-c i))) :=
      Finset.sum_le_sum fun i _ => capProduct_largeWeightHit_le hR hρ u c hc0 hc1 r z i
    _ = ENNReal.ofReal (∑ i, 6*ρ/(R*(1-c i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact div_nonneg (mul_nonneg (by norm_num) hρ) (mul_nonneg hR.le (sub_pos.mpr (hc1 i)).le)
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hR.ne', (sub_pos.mpr (hc1 i)).ne']
      <;> ring
end QEC.Coding.ProbabilisticConstruction.SphericalCap
