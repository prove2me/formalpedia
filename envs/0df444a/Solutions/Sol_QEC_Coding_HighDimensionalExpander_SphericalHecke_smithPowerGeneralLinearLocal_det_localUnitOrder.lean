-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.smithPowerGeneralLinearLocal_det_localUnitOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:52.299487+00:00
-- url     : https://prove2.me/submissions/abdff611-1afe-4237-a399-c06427367536

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_prod
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



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
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (smithPowerGeneralLinearLocal (k := k) (d := d) A)) =
      ∑ i, (smithExponent (k := k) (d := d) A i : ℤ) := by
  have hdet : Matrix.GeneralLinearGroup.det
      (smithPowerGeneralLinearLocal (k := k) (d := d) A) =
      ∏ i, uniformizerUnit k ^ smithExponent (k := k) (d := d) A i := by
    apply Units.ext
    simp [smithPowerGeneralLinearLocal, diagonalGeneralLinear,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [hdet, localUnitOrder_prod]
  apply Finset.sum_congr rfl
  intro i _
  exact localUnitOrder_uniformizerUnit_pow _
end QEC.Coding.HighDimensionalExpander.SphericalHecke
