-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.map_inv_smithDomainGeneralLinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:48.486609+00:00
-- url     : https://prove2.me/submissions/bbaebe63-6f67-47f3-a754-05e379625dcc

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_powerSeriesGeneralLinearToLocal

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
    (integerEmbedding k).mapMatrix
        (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
          GL (Fin d) (IntegerRing k)) :
            Matrix (Fin d) (Fin d) (IntegerRing k)) =
      ((smithRightGeneralLinearLocal (k := k) (d := d) A)⁻¹ :
        GL (Fin d) (LocalFunctionField k)) := by
  rw [← coe_powerSeriesGeneralLinearToLocal]
  apply congrArg Units.val
  change (powerSeriesGeneralLinearToLocal k d)
      ((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹) =
    ((powerSeriesGeneralLinearToLocal k d)
      (smithDomainGeneralLinear (k := k) (d := d) A))⁻¹
  exact map_inv _ _
end QEC.Coding.HighDimensionalExpander.SphericalHecke
