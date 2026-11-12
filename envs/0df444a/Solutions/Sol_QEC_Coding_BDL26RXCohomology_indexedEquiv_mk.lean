-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.indexedEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:49:59.025829+00:00
-- url     : https://prove2.me/submissions/ea1a8d2d-2283-4a55-b984-fcc70ac4463a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_nextEquiv_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
open BDL26IndexedDecoder MultiscaleDecoder
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0)
    (v : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    indexedEquiv S depth i h
      (((indexedFamily S depth).complex i.castSucc).middleCoboundaryInCocycles.mkQ v) =
      ((indexedFamily S depth).complex i.succ).middleCoboundaryInCocycles.mkQ
        (indexedCocycle S depth i v) := nextEquiv_mk S i.val (state S i.val) h v
end QEC.Coding.BDL26RXCohomology
