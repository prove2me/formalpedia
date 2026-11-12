-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.indexedStepEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:55:01.862236+00:00
-- url     : https://prove2.me/submissions/85be9943-cefa-4b39-8845-e8a1993f386a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    indexedStepEquiv S depth i
      (((indexedFamily S depth).complex i.castSucc).middleCoboundaryInCocycles.mkQ w) =
      ((indexedFamily S depth).complex i.succ).middleCoboundaryInCocycles.mkQ
        (indexedStepCocycle S depth i w) := stepEquiv_mk S i.val w
end QEC.Coding.BDL26FiniteCohomology
