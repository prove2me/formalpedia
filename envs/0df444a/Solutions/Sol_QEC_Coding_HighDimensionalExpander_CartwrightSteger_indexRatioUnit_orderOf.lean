-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexRatioUnit_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:34:56.630084+00:00
-- url     : https://prove2.me/submissions/e89cff29-7852-4b34-9a1a-b3f443e6d18d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) (level : Nat) :
    orderOf
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) =
      (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank :=
  (Classical.choose_spec (exists_indexRatioUnit P r level)).2
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
