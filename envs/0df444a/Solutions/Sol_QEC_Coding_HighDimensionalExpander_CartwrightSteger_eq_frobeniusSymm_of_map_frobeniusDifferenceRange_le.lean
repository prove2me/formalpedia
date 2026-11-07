-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_frobeniusSymm_of_map_frobeniusDifferenceRange_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:31:56.437275+00:00
-- url     : https://prove2.me/submissions/3512fcb7-8e2a-4a12-b527-24460f4b6a7c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusDifferenceRange_ne_top
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (a : ConstantExtension P r)
    (hstable : (frobeniusDifferenceRange P r).map
        (constantMultiplicationLinearMap P r a) ≤
      frobeniusDifferenceRange P r) :
    (constantFrobenius P r).symm a = a := by
  let σ := (constantFrobenius P r).symm
  let H := frobeniusDifferenceRange P r
  have hterm : ∀ x : ConstantExtension P r,
      (a - σ a) * σ x ∈ H := by
    intro x
    have hdiff : frobeniusDifferenceLinearMap P r (a * x) ∈ H :=
      ⟨a * x, rfl⟩
    have hx : frobeniusDifferenceLinearMap P r x ∈ H := ⟨x, rfl⟩
    have hmul : a * frobeniusDifferenceLinearMap P r x ∈ H := by
      exact hstable (Submodule.mem_map_of_mem hx)
    have hsub := H.sub_mem hdiff hmul
    simpa [H, σ, frobeniusDifferenceLinearMap, map_mul,
      mul_sub, sub_mul] using hsub
  by_contra hne
  have hc : a - σ a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  apply frobeniusDifferenceRange_ne_top P r
  apply top_unique
  intro y _
  let x : ConstantExtension P r :=
    constantFrobenius P r ((a - σ a)⁻¹ * y)
  have hx := hterm x
  simpa [H, x, σ, hc, mul_assoc] using hx
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
