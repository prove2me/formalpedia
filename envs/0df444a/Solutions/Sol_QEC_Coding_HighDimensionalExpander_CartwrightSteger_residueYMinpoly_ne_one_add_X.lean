-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_ne_one_add_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:40.334971+00:00
-- url     : https://prove2.me/submissions/9cd56f00-af21-437e-b364-17a78ecec8c3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYMinpoly_natDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Polynomial IntermediateField
open ResidueSelection
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) (level : Nat) :
    residueYMinpoly P r level ≠ 1 + Polynomial.X := by
  intro h
  have hdegree := residueYMinpoly_natDegree P r level
  rw [h] at hdegree
  have hone :
      (1 + Polynomial.X : PolynomialRing P).natDegree = 1 := by
    simpa [add_comm] using
      (Polynomial.natDegree_X_add_C (1 : BaseField P))
  rw [hone] at hdegree
  cases r <;>
    simp [Rank.residueExponent, Rank.matrixRank] at hdegree <;> omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
