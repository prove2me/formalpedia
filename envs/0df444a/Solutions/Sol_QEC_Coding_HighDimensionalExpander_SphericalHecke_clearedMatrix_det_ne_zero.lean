-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:58:05.739856+00:00
-- url     : https://prove2.me/submissions/d041f125-827f-4044-ab61-da9625c052ae

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_map_clearedMatrix

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (clearedMatrix (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).det ≠ 0 := by
  intro hdet
  have hmap := congrArg
    (SubringClass.subtype (Valued.integer (LocalFunctionField k))) hdet
  rw [map_zero, RingHom.map_det, map_clearedMatrix, Matrix.det_smul] at hmap
  have hu : (uniformizerUnit k : LocalFunctionField k) ≠ 0 := Units.ne_zero _
  have hupow :
      ((uniformizerUnit k : LocalFunctionField k) ^
        matrixClearingExponent
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) ^
            Fintype.card (Fin d) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ hu)
  exact (mul_ne_zero hupow A.det_ne_zero) hmap
end QEC.Coding.HighDimensionalExpander.SphericalHecke
