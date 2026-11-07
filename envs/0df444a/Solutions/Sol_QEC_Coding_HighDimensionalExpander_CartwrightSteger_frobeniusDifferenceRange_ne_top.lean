-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusDifferenceRange_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:26.477536+00:00
-- url     : https://prove2.me/submissions/bcae56e2-88c9-4895-8a26-20d0181f55f2

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusDifferenceLinearMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    frobeniusDifferenceRange P r ≠ ⊤ := by
  intro htop
  have hsurjective : Function.Surjective
      (frobeniusDifferenceLinearMap P r) := by
    rw [← LinearMap.range_eq_top]
    exact htop
  have hinjective : Function.Injective
      (frobeniusDifferenceLinearMap P r) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr
      hsurjective
  have hone : (1 : ConstantExtension P r) = 0 := by
    apply hinjective
    rw [frobeniusDifferenceLinearMap_one]
    simp [frobeniusDifferenceLinearMap]
  exact one_ne_zero hone
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
