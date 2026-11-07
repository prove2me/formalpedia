-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.orderTop_finset_sum_lowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:42.692798+00:00
-- url     : https://prove2.me/submissions/34b86dd8-5275-43ab-b680-5f17b2d19439

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
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
    {k : Type u} [Field k]
    {α : Type*} {s : Finset α} {f : α → LocalFunctionField k}
    {m : WithTop ℤ} (h : ∀ a ∈ s, m ≤ (f a).orderTop) :
    m ≤ (∑ a ∈ s, f a).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HahnSeries.orderTop_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (le_min (h a (Finset.mem_insert_self a s))
        (ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb)))).trans
          HahnSeries.min_orderTop_le_orderTop_add
end QEC.Coding.HighDimensionalExpander.SphericalHecke
