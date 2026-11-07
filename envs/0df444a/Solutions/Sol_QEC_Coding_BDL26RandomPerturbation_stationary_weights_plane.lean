-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.stationary_weights_plane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:40.310227+00:00
-- url     : https://prove2.me/submissions/ff455333-e338-4638-89ce-d2b70983c68a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_barycenter_affine_coordinates
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_plane_coefficients_unique


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3))
    (hi : ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) = 0)
    (hdet : gramDet (a 1-a 0) (a 2-a 0) ≠ 0) :
    w.val 1 = planeU (a 1-a 0) (a 2-a 0) (z-a 0) ∧
      w.val 2 = planeV (a 1-a 0) (a 2-a 0) (z-a 0) := by
  have h1 : inner ℝ (z-barycenterMap a w) (a 1-a 0) = 0 := by
    have he : a 1-a 0 = (a 1-barycenterMap a w)-(a 0-barycenterMap a w) := by abel
    rw [he,inner_sub_right,hi 1,hi 0,sub_self]
  have h2 : inner ℝ (z-barycenterMap a w) (a 2-a 0) = 0 := by
    have he : a 2-a 0 = (a 2-barycenterMap a w)-(a 0-barycenterMap a w) := by abel
    rw [he,inner_sub_right,hi 2,hi 0,sub_self]
  have he : z-barycenterMap a w =
      (z-a 0)-(w.val 1 • (a 1-a 0)+w.val 2 • (a 2-a 0)) := by
    rw [barycenter_affine_coordinates]
    abel
  rw [he] at h1 h2
  rw [inner_sub_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,real_inner_comm (a 1-a 0) (a 2-a 0)] at h1
  rw [inner_sub_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h2
  apply plane_coefficients_unique _ _ _ hdet <;> linarith
end QEC.Coding.BDL26RandomPerturbation
