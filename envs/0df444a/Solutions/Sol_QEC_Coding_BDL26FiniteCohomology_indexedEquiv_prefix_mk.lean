-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.indexedEquiv_prefix_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:55:05.091491+00:00
-- url     : https://prove2.me/submissions/fe91b848-f0fb-44ba-8a34-66e47dd8b7f4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_prefix_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : Cocycle S 0) :
    indexedEquiv S depth i
      (((indexedFamily S depth).complex i).middleCoboundaryInCocycles.mkQ
        (prefixCocycle S i.val w)) = BDL26SeedCohomology.coefficient w.1 :=
  finiteH1Equiv_prefix_mk S i.val w
end QEC.Coding.BDL26FiniteCohomology
