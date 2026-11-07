-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.largeWeightHit_section_subset_slab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:51.195843+00:00
-- url     : https://prove2.me/submissions/207f6d8e-d71b-4847-8ab8-52f6e90005ee

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Mathlib.Probability.Independence.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleProduct
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_exists_unit_normal_except
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_large_weight_slab
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (r : Fin 3 → Space) (z : Space)
    (ρ : ℝ) (i : Fin 3) (q : Fin 2 → Space) :
    ∃ n : Sphere, {p : Space | i.insertNth (α := fun _ : Fin 3 => Space) p q ∈ largeWeightHit r z ρ i} ⊆
      slab n (inner ℝ (n : Space) (z-r i)) (3*ρ) := by
  obtain ⟨n,hn⟩ := exists_unit_normal_except (fun j => r j+i.insertNth (α := fun _ : Fin 3 => Space) (0:Space) q j) z i
  refine ⟨n, ?_⟩
  intro p hp
  obtain ⟨w,hw,hball⟩ := hp
  have hnormal : ∀ j, j ≠ i →
      inner ℝ (n : Space) (r j+i.insertNth (α := fun _ : Fin 3 => Space) p q j-z) = 0 := by
    intro j hj
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simpa only [Fin.insertNth_apply_succAbove] using hn (i.succAbove k) (Fin.succAbove_ne i k)
  have hb := large_weight_slab w hw hball n hnormal
  simp only [Fin.insertNth_apply_same] at hb
  change |inner ℝ (n : Space) p - inner ℝ (n : Space) (z-r i)| ≤ 3*ρ
  convert hb using 1 <;> simp only [inner_sub_right,inner_add_right] <;> ring
end QEC.Coding.ProbabilisticConstruction.SphericalCap
