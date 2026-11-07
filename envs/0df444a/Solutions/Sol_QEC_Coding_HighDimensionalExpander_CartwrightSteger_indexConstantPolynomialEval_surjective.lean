-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantPolynomialEval_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:10.395982+00:00
-- url     : https://prove2.me/submissions/fc34650c-ada8-46e6-9cf9-e50ad5635860

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantPolynomialEval_map_base

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexConstantPolynomialEval P r level) := by
  intro x
  obtain ⟨f, hf⟩ := indexPolynomialEval_surjective P r level x
  exact ⟨Polynomial.map
    (algebraMap (BaseField P) (ConstantExtension P r)) f,
      (indexConstantPolynomialEval_map_base P r level f).trans hf⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
