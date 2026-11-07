-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_action_eq_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:52:56.555488+00:00
-- url     : https://prove2.me/submissions/d6683638-a166-4787-8929-1a55353e299d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.Algebra.Ring.Action.End
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    Multiplicative.ofAdd (1 : ℤ) • c = constantFrobenius P r c := by
  change constantFrobeniusZRingAction P r (Multiplicative.ofAdd 1) c = _
  rw [constantFrobeniusZRingAction, zpowersHom_apply]
  simp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
