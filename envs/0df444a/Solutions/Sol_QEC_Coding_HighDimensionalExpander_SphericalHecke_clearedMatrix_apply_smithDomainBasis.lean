-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_apply_smithDomainBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:41.986598+00:00
-- url     : https://prove2.me/submissions/e4c33de1-12c5-485b-85c2-cc81d164213d

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
    Matrix.mulVec
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)))
        (smithDomainBasis (k := k) (d := d) A i) =
      smithDiagonalCoeff (k := k) (d := d) A i •
        smithAmbientBasis (k := k) (d := d) A i := by
  change ((clearedImageEquiv (k := k) (d := d) A)
      (smithDomainBasis (k := k) (d := d) A i) :
        Fin d → IntegerRing k) = _
  rw [smithDomainBasis, Basis.map_apply, LinearEquiv.apply_symm_apply]
  exact (clearedImage (k := k) (d := d) A).smithNormalFormBotBasis_def
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A) i
end QEC.Coding.HighDimensionalExpander.SphericalHecke
