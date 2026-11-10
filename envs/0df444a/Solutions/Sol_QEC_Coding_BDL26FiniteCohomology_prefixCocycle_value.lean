-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.prefixCocycle_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:26:52.938834+00:00
-- url     : https://prove2.me/submissions/65e9c13a-e4b3-4c26-95f2-25a0f0f55e97

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (n : Nat) (w : Cocycle S 0) :
    (prefixCocycle S n w).1 = BDL26AlternatingCochain.map1 S n w.1 := rfl
end QEC.Coding.BDL26FiniteCohomology
