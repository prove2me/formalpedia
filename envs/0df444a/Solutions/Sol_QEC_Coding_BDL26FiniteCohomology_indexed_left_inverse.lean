-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.indexed_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:49:00.479931+00:00
-- url     : https://prove2.me/submissions/44606734-a82c-45bb-86ec-92edc0e2341e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (v : ((indexedFamily S depth).complex i).middleCohomology) :
    (indexedEquiv S depth i).symm (indexedEquiv S depth i v) = v :=
  (indexedEquiv S depth i).symm_apply_apply v
end QEC.Coding.BDL26FiniteCohomology
