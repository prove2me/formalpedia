-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.smithDiagonalCoeff_eq_unit_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:43.029213+00:00
-- url     : https://prove2.me/submissions/b9dc792f-1c7d-4161-8795-5b6d1bbf7580

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
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) :
    smithDiagonalCoeff (k := k) (d := d) A i =
      (smithCoeffUnit (k := k) (d := d) A i : IntegerRing k) *
        PowerSeries.X ^ smithExponent (k := k) (d := d) A i :=
  Classical.choose_spec
    (Classical.choose_spec
      (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (smithDiagonalCoeff_ne_zero (k := k) (d := d) A i)
        (PowerSeries.X_irreducible (R := k))))
end QEC.Coding.HighDimensionalExpander.SphericalHecke
