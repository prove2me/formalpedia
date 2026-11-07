-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_frobeniusNormalBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:53.932805+00:00
-- url     : https://prove2.me/submissions/be8ddab5-4a40-4aed-8658-384ff7fa299c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusNormalBasis_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (i : Fin r.matrixRank) :
    constantFrobenius P r (frobeniusNormalBasis P r i) =
      frobeniusNormalBasis P r (finRotate r.matrixRank i) := by
  rw [frobeniusNormalBasis_apply, frobeniusNormalBasis_apply,
    finRotate_apply]
  change ((constantFrobenius P r) *
      (constantFrobenius P r) ^ i.val)
        (IsGalois.normalBasis (BaseField P) (ConstantExtension P r) 1) = _
  rw [← pow_succ']
  cases r with
  | three =>
      fin_cases i
      · simp
      · simp
      · simpa using congrArg
          (fun e : ConstantGaloisGroup P .three =>
            e (IsGalois.normalBasis (BaseField P)
              (ConstantExtension P .three) 1))
          (constantFrobenius_pow_matrixRank P .three)
  | four =>
      fin_cases i
      · simp
      · simp
      · simp
      · simpa using congrArg
          (fun e : ConstantGaloisGroup P .four =>
            e (IsGalois.normalBasis (BaseField P)
              (ConstantExtension P .four) 1))
          (constantFrobenius_pow_matrixRank P .four)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
