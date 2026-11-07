-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlacePolynomial_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:42.59087+00:00
-- url     : https://prove2.me/submissions/c14c07a2-b317-434a-ab71-db4bdacab0c6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Irreducible (indexPlacePolynomial P r level) :=
  minpoly.irreducible (Algebra.IsIntegral.isIntegral (indexPlaceY P r level))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
