-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integralGeneralLinearToLocal_orderLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:47:30.083929+00:00
-- url     : https://prove2.me/submissions/4d5b7236-2dc3-4047-88de-de69e60ac111

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_orderTop_nonneg_of_mem_integer

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    MatrixOrderLowerBound 0
      (integralGeneralLinearToLocal k d A :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  intro i j
  apply orderTop_nonneg_of_mem_integer
  exact (A i j).property
end QEC.Coding.HighDimensionalExpander.SphericalHecke
