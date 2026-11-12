-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_buildingLatticeQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:58:29.655245+00:00
-- url     : https://prove2.me/submissions/24914947-a5f2-4384-92c9-f7d911e7d368

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (BuildingCartwrightStegerLattice P r ⧸
          BuildingCartwrightStegerCongruenceSubgroup P r level) =
      Nat.card (IndexCartwrightStegerImage P r level) :=
  Nat.card_congr (buildingLatticeQuotientEquiv P r level).toEquiv
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
