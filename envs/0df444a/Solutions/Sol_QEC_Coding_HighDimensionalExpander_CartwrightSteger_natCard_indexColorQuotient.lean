-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_indexColorQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:49:36.694856+00:00
-- url     : https://prove2.me/submissions/569e1a68-4b31-4ce3-b0a1-fcedd776b1c4

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (IndexCartwrightStegerImage P r level ⧸
          IndexCartwrightStegerColorZero P r level) =
      Nat.card (ResiduePowerClass P r level) :=
  Nat.card_congr (indexColorQuotientEquiv P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
