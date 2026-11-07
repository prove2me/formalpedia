-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_toLin_one_sub_frobeniusGL_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:46.367824+00:00
-- url     : https://prove2.me/submissions/a661274e-5bdc-493c-8027-add3344e4a1f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_toLin_one_sub_frobeniusGL_inv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    LinearMap.range
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          (1 - ((frobeniusGL P r)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P)))) =
      frobeniusDifferenceRange P r := by
  rw [toLin_one_sub_frobeniusGL_inv]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
