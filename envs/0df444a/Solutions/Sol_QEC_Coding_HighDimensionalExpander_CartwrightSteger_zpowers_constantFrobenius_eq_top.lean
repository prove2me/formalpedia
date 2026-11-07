-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.zpowers_constantFrobenius_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:35.13084+00:00
-- url     : https://prove2.me/submissions/3e9a2aa5-2b1a-44eb-9999-ca1255eabb44

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_order


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Subgroup.zpowers (constantFrobenius P r) = ⊤ := by
  apply (Subgroup.card_eq_iff_eq_top
    (Subgroup.zpowers (constantFrobenius P r))).mp
  rw [Nat.card_zpowers, constantFrobenius_order,
    IsGalois.card_aut_eq_finrank,
    GaloisField.finrank P.q (by cases r <;> simp [Rank.matrixRank])]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
