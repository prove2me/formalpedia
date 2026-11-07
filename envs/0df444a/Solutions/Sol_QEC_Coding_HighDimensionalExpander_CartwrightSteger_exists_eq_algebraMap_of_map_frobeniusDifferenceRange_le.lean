-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_eq_algebraMap_of_map_frobeniusDifferenceRange_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:44:24.757961+00:00
-- url     : https://prove2.me/submissions/a9aeca1b-03d4-4d57-8c23-b051bfa0fc22

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_eq_frobeniusSymm_of_map_frobeniusDifferenceRange_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_eq_algebraMap_of_constantFrobenius_eq
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
    ∃ c : BaseField P,
      a = algebraMap (BaseField P) (ConstantExtension P r) c := by
  have hsymm :=
    eq_frobeniusSymm_of_map_frobeniusDifferenceRange_le P r a hstable
  have hforward : constantFrobenius P r a = a := by
    have h := congrArg (constantFrobenius P r) hsymm
    simpa using h.symm
  obtain ⟨c, hc⟩ :=
    exists_eq_algebraMap_of_constantFrobenius_eq P r a hforward
  exact ⟨c, hc.symm⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
