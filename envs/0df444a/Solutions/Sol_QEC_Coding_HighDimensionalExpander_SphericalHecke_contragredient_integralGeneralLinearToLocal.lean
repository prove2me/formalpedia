-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.contragredient_integralGeneralLinearToLocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:36.842211+00:00
-- url     : https://prove2.me/submissions/49512700-bf86-4d35-9683-1be1df8a8733

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
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    contragredientGeneralLinearHom (integralGeneralLinearToLocal k d A) =
      integralGeneralLinearToLocal k d
        (contragredientGeneralLinearHom A) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (((integralGeneralLinearToLocal k d A)⁻¹ :
    GL (Fin d) (LocalFunctionField k)) :
    Matrix (Fin d) (Fin d) (LocalFunctionField k)) j i = _
  rw [← map_inv]
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
