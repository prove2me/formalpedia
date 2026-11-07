-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_ne_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:37.026138+00:00
-- url     : https://prove2.me/submissions/b8e45e0c-f862-4b2f-ac47-34868a7340dd

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
    residueYMinpoly P r level ≠ Polynomial.X := by
  intro h
  have hdegree := residueYMinpoly_natDegree P r level
  rw [h, Polynomial.natDegree_X] at hdegree
  cases r <;>
    simp [Rank.residueExponent, Rank.matrixRank] at hdegree <;> omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
