-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.positive_weights_stationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:11.282902+00:00
-- url     : https://prove2.me/submissions/81bcb48a-ce09-4611-9059-6793e00ace9c

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
theorem _root_.solution (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3)) (hw : ∀ i, 0 < w.val i)
    (hi : ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) ≤ 0) :
    ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) = 0 := by
  let y := barycenterMap a w
  have hsum : ∑ i, w.val i • (a i-y) = 0 := by
    simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,w.property.2,one_smul]
    change barycenterMap a w-y = 0
    exact sub_self _
  have hs : ∑ i, w.val i*inner ℝ (z-y) (a i-y) = 0 := by
    have h := congrArg (inner ℝ (z-y)) hsum
    simpa only [inner_sum,real_inner_smul_right,inner_zero_right] using h
  have hn : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      w.val i*inner ℝ (z-y) (a i-y) ≤ 0 := by
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (hw i).le (hi i)
  have he := (Finset.sum_eq_zero_iff_of_nonpos hn).mp hs
  intro i
  exact (mul_eq_zero.mp (he i (Finset.mem_univ i))).resolve_left (ne_of_gt (hw i))
end QEC.Coding.BDL26RandomPerturbation
