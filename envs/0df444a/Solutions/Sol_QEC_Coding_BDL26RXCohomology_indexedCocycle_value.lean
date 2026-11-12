-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.indexedCocycle_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:49:24.361806+00:00
-- url     : https://prove2.me/submissions/26125bf3-18bc-4df1-9fc2-e13a56758f6d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq


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
    (v : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    (indexedCocycle S depth i v).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 v.1 := by
  rw [selectedMap_eq]
  rfl
end QEC.Coding.BDL26RXCohomology
