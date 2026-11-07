-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.MatrixOrderLowerBound.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:51:37.66934+00:00
-- url     : https://prove2.me/submissions/2875588a-5c12-4cb0-ac1a-13a16f607279

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
namespace MatrixOrderLowerBound
theorem _root_.solution
    {k : Type u} [Field k] {d : ℕ} {m : WithTop ℤ}
    {A B : Matrix (Fin d) (Fin d) (LocalFunctionField k)}
    (hA : MatrixOrderLowerBound m A)
    (hB : MatrixOrderLowerBound m B) :
    MatrixOrderLowerBound m (A + B) := by
  intro i j
  exact (le_min (hA i j) (hB i j)).trans
    HahnSeries.min_orderTop_le_orderTop_add
end MatrixOrderLowerBound
end QEC.Coding.HighDimensionalExpander.SphericalHecke
