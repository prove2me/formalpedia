-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.card_upperUnipotentSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:47:48.0847+00:00
-- url     : https://prove2.me/submissions/3f78a874-c298-4a8b-b319-3260ce8f653b

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution [Fintype R] :
    Fintype.card (upperUnipotentSubgroup (R := R)) = Fintype.card R := by
  exact (Fintype.card_congr (upperUnipotentEquiv (R := R))).symm
end QEC.Coding.BalancedProduct.LPSArithmetic
