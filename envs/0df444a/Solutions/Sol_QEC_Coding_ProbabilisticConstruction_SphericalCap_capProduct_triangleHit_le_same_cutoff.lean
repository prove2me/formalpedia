-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capProduct_triangleHit_le_same_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:00.267727+00:00
-- url     : https://prove2.me/submissions/5b8eaa94-e074-4179-88d6-21b092e2ac17

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capProduct_triangleHit_le
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
theorem _root_.solution {R ρ c : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    (u : Fin 3 → Sphere) (hc0 : -1 < c) (hc1 : c < 1)
    (r : Fin 3 → Space) (z : Space) :
    Measure.pi (fun j => capDisplacementLaw R (u j) c) (triangleHit r z ρ) ≤
      ENNReal.ofReal (18*ρ/(R*(1-c))) := by
  have hb := capProduct_triangleHit_le hR hρ u (fun _ => c) (fun _ => hc0) (fun _ => hc1) r z
  have he : (6*ρ/R) * ∑ _ : Fin 3, 1/(1-c) = 18*ρ/(R*(1-c)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hR.ne', (sub_pos.mpr hc1).ne']
    <;> ring
  rwa [he] at hb
end QEC.Coding.ProbabilisticConstruction.SphericalCap
