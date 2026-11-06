-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.card_upperUnipotentSubgroup_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:53:37.855203+00:00
-- url     : https://prove2.me/submissions/df977fdc-0520-4fc3-a804-d512026b5715

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_card_upperUnipotentSubgroup

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution (q : ℕ) [NeZero q] :
    Fintype.card (upperUnipotentSubgroup (R := ZMod q)) = q := by
  rw [card_upperUnipotentSubgroup, ZMod.card]
end QEC.Coding.BalancedProduct.LPSArithmetic
