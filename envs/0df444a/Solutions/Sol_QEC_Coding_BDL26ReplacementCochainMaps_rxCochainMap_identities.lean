-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementCochainMaps.rxCochainMap_identities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:01:32.570676+00:00
-- url     : https://prove2.me/submissions/a8b24222-8574-4a44-85bc-3e7a623b3b63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary0
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary1

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder
namespace QEC.Coding.BDL26ReplacementCochainMaps
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    (rxCoboundary0 P S).comp (rxMap P S).map0 =
        (rxMap P S).map1.comp (tannerCoboundary0 P) ∧
      (rxCoboundary1 P S).comp (rxMap P S).map1 =
        (rxMap P S).map2.comp (tannerCoboundary1 P) := by
  exact ⟨rxMap_commutes_coboundary0 P A S, rxMap_commutes_coboundary1 P S⟩
end QEC.Coding.BDL26ReplacementCochainMaps
