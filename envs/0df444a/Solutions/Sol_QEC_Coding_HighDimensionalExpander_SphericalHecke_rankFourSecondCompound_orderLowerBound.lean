-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompound_orderLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:48:57.600206+00:00
-- url     : https://prove2.me/submissions/8f2b0f75-d34c-4d82-8061-022a4ccd6b06

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] {m : WithTop ℤ}
    {A : Matrix (Fin 4) (Fin 4) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound m A) :
    MatrixOrderLowerBound (m + m) (rankFourSecondCompound A) := by
  intro p q
  apply (le_min ?_ ?_).trans
    HahnSeries.min_orderTop_le_orderTop_sub
  · rw [HahnSeries.orderTop_mul]
    exact add_le_add (hA _ _) (hA _ _)
  · rw [HahnSeries.orderTop_mul]
    exact add_le_add (hA _ _) (hA _ _)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
