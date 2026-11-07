-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantArithmeticEval_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:28.859429+00:00
-- url     : https://prove2.me/submissions/2c6cce9d-8650-41be-973d-7c5c0c1204f3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantPolynomialEval_surjective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexConstantArithmeticEval P r level) := by
  intro x
  obtain ⟨f, rfl⟩ := indexConstantPolynomialEval_surjective P r level x
  exact ⟨algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r) f,
    indexConstantArithmeticEval_algebraMap P r level f⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
