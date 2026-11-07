-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_orderSplitLatticeQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:40.89516+00:00
-- url     : https://prove2.me/submissions/2b221ca1-d42d-48ab-bc60-76772d51712f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (OrderSplitCartwrightStegerLattice P r ⧸
          OrderSplitCartwrightStegerCongruenceSubgroup P r level) =
      Nat.card (IndexCartwrightStegerImage P r level) :=
  Nat.card_congr (orderSplitLatticeQuotientEquiv P r level).toEquiv
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
