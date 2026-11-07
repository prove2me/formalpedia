-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedPowerSeriesMatrix_power_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:59.463614+00:00
-- url     : https://prove2.me/submissions/169e5835-9a17-4176-b5fc-855d49ce641b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_clearedPowerSeriesMatrix_smith_factorization
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonal_smithDiagonalCoeff_factorization

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
      (smithLeftGeneralLinear (k := k) (d := d) A :
          Matrix (Fin d) (Fin d) (IntegerRing k)) *
        smithPowerDiagonal (k := k) (d := d) A *
      (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
          GL (Fin d) (IntegerRing k)) :
            Matrix (Fin d) (Fin d) (IntegerRing k)) := by
  rw [clearedPowerSeriesMatrix_smith_factorization (k := k) (d := d) A,
    diagonal_smithDiagonalCoeff_factorization (k := k) (d := d) A]
  change _ * (_ * _) * _ = (_ * _) * _ * _
  ac_rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
