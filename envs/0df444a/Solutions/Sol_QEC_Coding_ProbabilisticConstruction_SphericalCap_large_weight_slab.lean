-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.large_weight_slab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:40:49.713284+00:00
-- url     : https://prove2.me/submissions/8ba881fe-f9a7-4e12-82e2-987e2dff16f8

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenter_sub
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply


attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {a : Fin 3 → Space} {z : Space} {ρ : ℝ} {i : Fin 3}
    (w : stdSimplex ℝ (Fin 3)) (hw : (1:ℝ)/3 ≤ (w : Fin 3 → ℝ) i)
    (hball : dist (∑ j, (w : Fin 3 → ℝ) j • a j) z ≤ ρ)
    (n : Sphere) (hn : ∀ j, j ≠ i → inner ℝ (n : Space) (a j-z) = 0) :
    |inner ℝ (n : Space) (a i-z)| ≤ 3*ρ := by
  have he : inner ℝ (n : Space) ((∑ j, (w : Fin 3 → ℝ) j • a j)-z) =
      (w : Fin 3 → ℝ) i * inner ℝ (n : Space) (a i-z) := by
    rw [barycenter_sub a z w, inner_sum]
    simp_rw [real_inner_smul_right]
    exact Finset.sum_eq_single i (fun j _ hji => by rw [hn j hji,mul_zero])
      (by simp)
  have hb := abs_real_inner_le_norm (n : Space)
    ((∑ j, (w : Fin 3 → ℝ) j • a j)-z)
  rw [he,norm_coe,one_mul,abs_mul] at hb
  erw [abs_of_nonneg (w.property.1 i)] at hb
  have hh : ‖(∑ j, (w : Fin 3 → ℝ) j • a j)-z‖ ≤ ρ := hball
  have hsmall : (1:ℝ)/3 * |inner ℝ (n : Space) (a i-z)| ≤ ρ :=
    (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans (hb.trans hh)
  linarith
end QEC.Coding.ProbabilisticConstruction.SphericalCap
