-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_indexGeneratorFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:58:49.235885+00:00
-- url     : https://prove2.me/submissions/0a02e95a-475c-4d1b-8766-cdb7eae5669e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_indexGeneratorFinset

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexGeneratorFinset P r level).card ≤
      Fintype.card (ConstantProjectiveClass P r) := by
  exact (card_indexGeneratorFinset P r level).le
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
