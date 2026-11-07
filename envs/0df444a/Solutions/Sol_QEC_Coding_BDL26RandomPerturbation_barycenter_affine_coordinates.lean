-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.barycenter_affine_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:21.322551+00:00
-- url     : https://prove2.me/submissions/d4827628-600f-4bd2-b6e4-a68ff185d59c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
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
theorem _root_.solution (a : Fin 3 → Space)
    (w : stdSimplex ℝ (Fin 3)) :
    barycenterMap a w = a 0+w.val 1 • (a 1-a 0)+w.val 2 • (a 2-a 0) := by
  have hs := w.property.2
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
  change w.val 0+(w.val 1+w.val 2) = 1 at hs
  rw [barycenterMap_apply]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  have h0 : w.val 0 = 1-w.val 1-w.val 2 := by linarith
  change w.val 0 • a 0+(w.val 1 • a 1+w.val 2 • a 2) = _
  rw [h0]
  module
end QEC.Coding.BDL26RandomPerturbation
