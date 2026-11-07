-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlaceY_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:38:43.851107+00:00
-- url     : https://prove2.me/submissions/8e844a21-699f-4f4c-93e0-000466a83031

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
    indexPlaceY P r level ≠ 0 := by
  intro hzero
  have hdegree := indexPlacePolynomial_natDegree P r level
  rw [indexPlacePolynomial, hzero, minpoly.zero, Polynomial.natDegree_X] at hdegree
  cases r <;>
    simp [Rank.residueExponent, Rank.matrixRank] at hdegree <;> omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
