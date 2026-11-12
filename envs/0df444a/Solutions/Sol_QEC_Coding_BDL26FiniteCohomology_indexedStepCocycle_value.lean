-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.indexedStepCocycle_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:54:55.433613+00:00
-- url     : https://prove2.me/submissions/c8506194-e0c6-4c61-a10e-71ff1924f993

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    (indexedStepCocycle S depth i w).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 w.1 := by
  rw [selectedMap_eq]
  rfl
end QEC.Coding.BDL26FiniteCohomology
