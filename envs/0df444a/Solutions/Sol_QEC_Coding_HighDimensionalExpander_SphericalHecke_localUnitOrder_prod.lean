-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:46:13.75492+00:00
-- url     : https://prove2.me/submissions/d971ef18-204f-4232-8123-ab8d534b57b6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_mul
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
    {k : Type u} [Field k] {α : Type*}
    (s : Finset α) (f : α → Units (LocalFunctionField k)) :
    localUnitOrder (∏ i ∈ s, f i) =
      ∑ i ∈ s, localUnitOrder (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localUnitOrder]
  | @insert a s ha ih =>
      simp [ha, localUnitOrder_mul, ih]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
