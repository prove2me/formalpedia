-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlacePolynomial_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:37:58.888272+00:00
-- url     : https://prove2.me/submissions/6905fdb5-710a-4b9e-a75d-b4213b606da7

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_adjoin_eq_top
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_residueExponent_ne_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexPlacePolynomial P r level).natDegree =
      r.residueExponent level := by
  rw [indexPlacePolynomial]
  calc
    (minpoly (BaseField P) (indexPlaceY P r level)).natDegree =
        Module.finrank (BaseField P) (ResidueField P r level) :=
      (Field.primitive_element_iff_minpoly_natDegree_eq
        (BaseField P) (indexPlaceY P r level)).mp
          (indexPlaceY_adjoin_eq_top P r level)
    _ = r.residueExponent level :=
      GaloisField.finrank P.q (Rank.residueExponent_ne_zero r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
