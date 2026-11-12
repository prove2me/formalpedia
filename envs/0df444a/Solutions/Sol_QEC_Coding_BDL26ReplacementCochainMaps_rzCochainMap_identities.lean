-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementCochainMaps.rzCochainMap_identities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:01:35.721454+00:00
-- url     : https://prove2.me/submissions/e1198965-349e-4616-8a03-ddc22b166cdc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary0
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary1

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
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    (rzCoboundary0 P A4 S).comp (rzCochainMap P A4 S).map0 =
        (rzCochainMap P A4 S).map1.comp (tannerCoboundary0 P) ∧
      (rzCoboundary1 P A4 S).comp (rzCochainMap P A4 S).map1 =
        (rzCochainMap P A4 S).map2.comp (tannerCoboundary1 P) := by
  exact ⟨rzMap_commutes_coboundary0 P A4 S, rzMap_commutes_coboundary1 P A4 S⟩
end QEC.Coding.BDL26ReplacementCochainMaps
