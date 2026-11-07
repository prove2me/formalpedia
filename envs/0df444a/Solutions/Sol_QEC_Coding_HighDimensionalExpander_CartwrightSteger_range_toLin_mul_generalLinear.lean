-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_mul_generalLinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:40.446192+00:00
-- url     : https://prove2.me/submissions/2738f939-35a4-43d0-9a1d-e3c541decb6f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))
    (C : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (BaseField P)) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (A * (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BaseField P)))) =
      LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r) A) := by
  rw [Matrix.toLin_mul (constantBasis P r) (constantBasis P r)
    (constantBasis P r)]
  apply LinearMap.range_comp_of_range_eq_top
  rw [LinearMap.range_eq_top]
  intro x
  refine ⟨Matrix.toLin (constantBasis P r) (constantBasis P r)
    ((C⁻¹ : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (BaseField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) x, ?_⟩
  rw [← Matrix.toLin_mul_apply]
  simp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
