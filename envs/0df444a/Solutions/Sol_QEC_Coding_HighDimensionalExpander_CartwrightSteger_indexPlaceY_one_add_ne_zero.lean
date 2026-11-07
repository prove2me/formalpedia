-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlaceY_one_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:38:42.847195+00:00
-- url     : https://prove2.me/submissions/7f48935d-5f78-4978-a8d9-9c19f1e45876

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlacePolynomial_natDegree
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    1 + indexPlaceY P r level ≠ 0 := by
  intro hzero
  have hy : indexPlaceY P r level = -1 :=
    eq_neg_of_add_eq_zero_right hzero
  have hinRange : indexPlaceY P r level ∈
      (algebraMap (BaseField P) (ResidueField P r level)).range := by
    refine ⟨-1, ?_⟩
    simp [hy]
  have hdegreeOne :
      (minpoly (BaseField P) (indexPlaceY P r level)).natDegree = 1 :=
    minpoly.natDegree_eq_one_iff.mpr hinRange
  have hdegree := indexPlacePolynomial_natDegree P r level
  change (minpoly (BaseField P) (indexPlaceY P r level)).natDegree =
    r.residueExponent level at hdegree
  rw [hdegreeOne] at hdegree
  cases r <;>
    simp [Rank.residueExponent, Rank.matrixRank] at hdegree <;> omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
