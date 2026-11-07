-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.segmentPoint_mem_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:20.322613+00:00
-- url     : https://prove2.me/submissions/0a7b3a87-3ff9-4bb5-9664-0152e7846ad2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_clampUnit_bounds
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a : Fin 3 → Space) (z : Space) (i j : Fin 3) :
    segmentPoint (a i) (a j) z ∈ convexHull ℝ (range a) := by
  apply (convex_convexHull ℝ (range a)).add_smul_mem
    (subset_convexHull ℝ _ (mem_range_self i))
    (by simpa using subset_convexHull ℝ (range a) (mem_range_self j))
  exact clampUnit_bounds _
end QEC.Coding.BDL26RandomPerturbation
