-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.MatrixOrderLowerBound.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:35.312902+00:00
-- url     : https://prove2.me/submissions/fe052939-ad0a-4019-88e0-3423065ce12c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_orderTop_finset_sum_lowerBound

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
namespace MatrixOrderLowerBound
theorem _root_.solution
    {k : Type u} [Field k] {d : ℕ} {a b : WithTop ℤ}
    {A B : Matrix (Fin d) (Fin d) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound a A)
    (hB : MatrixOrderLowerBound b B) :
    MatrixOrderLowerBound (a + b) (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  apply orderTop_finset_sum_lowerBound
  intro z _
  rw [HahnSeries.orderTop_mul]
  exact add_le_add (hA i z) (hB z j)
end MatrixOrderLowerBound
end QEC.Coding.HighDimensionalExpander.SphericalHecke
