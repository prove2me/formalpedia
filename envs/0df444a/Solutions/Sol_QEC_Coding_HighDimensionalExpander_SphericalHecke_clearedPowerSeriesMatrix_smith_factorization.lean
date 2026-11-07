-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedPowerSeriesMatrix_smith_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:07.286201+00:00
-- url     : https://prove2.me/submissions/9d67d514-eff4-4e57-a27b-6f838e3409db

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_clearedMatrix_smith_coordinate_matrix

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
    clearedPowerSeriesMatrix (k := k) (d := d)
        (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) =
      (smithAmbientGeneralLinear (k := k) (d := d) A :
          Matrix (Fin d) (Fin d) (IntegerRing k)) *
        Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) *
      (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
          GL (Fin d) (IntegerRing k)) :
            Matrix (Fin d) (Fin d) (IntegerRing k)) := by
  symm
  change (Pi.basisFun (IntegerRing k) (Fin d)).toMatrix
        (smithAmbientBasis (k := k) (d := d) A) *
      Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) *
      (smithDomainBasis (k := k) (d := d) A).toMatrix
        (Pi.basisFun (IntegerRing k) (Fin d)) = _
  rw [← clearedMatrix_smith_coordinate_matrix (k := k) (d := d) A]
  calc
    _ = LinearMap.toMatrix
          (Pi.basisFun (IntegerRing k) (Fin d))
          (Pi.basisFun (IntegerRing k) (Fin d))
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin :=
      basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        (Pi.basisFun (IntegerRing k) (Fin d))
        (smithDomainBasis (k := k) (d := d) A)
        (Pi.basisFun (IntegerRing k) (Fin d))
        (smithAmbientBasis (k := k) (d := d) A)
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin
    _ = clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
      rw [LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply',
        LinearMap.toMatrix'_toLin']
end QEC.Coding.HighDimensionalExpander.SphericalHecke
