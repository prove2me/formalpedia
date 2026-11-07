-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:41:07.434592+00:00
-- url     : https://prove2.me/submissions/4dceee67-ff4f-46ea-854f-4d17482cdf21

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
    {R : Type u} [CommRing R] (A : GL (Fin 4) R) :
    (((rankFourSecondCompoundGeneralLinear A)⁻¹ : GL (Fin 6) R) :
      Matrix (Fin 6) (Fin 6) R) =
      rankFourSecondCompound
        (((A⁻¹ : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R)) := by
  change (rankFourSecondCompoundGeneralLinear A).inv =
    rankFourSecondCompound A.inv
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
