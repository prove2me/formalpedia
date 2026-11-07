-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.planePoint_mem_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:21.447299+00:00
-- url     : https://prove2.me/submissions/9e0fcdb9-46ab-4a25-ab8d-c73e42586647

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_barycenter_affine_coordinates
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_convexHull_range_eq_barycenters
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a : Fin 3 → Space) (z : Space)
    (h : planeFeasible a z) : planePoint a z ∈ convexHull ℝ (range a) := by
  let u := planeU (a 1-a 0) (a 2-a 0) (z-a 0)
  let v := planeV (a 1-a 0) (a 2-a 0) (z-a 0)
  let w : Fin 3 → ℝ := ![1-u-v,u,v]
  have hw : w ∈ stdSimplex ℝ (Fin 3) := by
    constructor
    · intro i
      fin_cases i
      · change 0 ≤ 1-u-v
        have ht : u+v ≤ 1 := h.2.2.2
        linarith
      · change 0 ≤ u
        exact h.2.1
      · change 0 ≤ v
        exact h.2.2.1
    · simp [w,Fin.sum_univ_succ]
  have he : barycenterMap a w = planePoint a z := by
    have hcoords := barycenter_affine_coordinates a ⟨w,hw⟩
    change barycenterMap a w = a 0+u • (a 1-a 0)+v • (a 2-a 0) at hcoords
    exact hcoords
  rw [← he,convexHull_range_eq_barycenters]
  exact ⟨w,hw,rfl⟩
end QEC.Coding.BDL26RandomPerturbation
