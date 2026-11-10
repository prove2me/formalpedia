-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.generator_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:26:18.178884+00:00
-- url     : https://prove2.me/submissions/c599ecab-524b-4ea5-956f-7d7f53300fa4

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
theorem _root_.solution (S : OddScale) (n : Nat) (c : Field) :
    (generator S n c).1 = BDL26AlternatingCochain.map1 S n
      (c • BDL26SeedCohomology.seedElement).1 := rfl
end QEC.Coding.BDL26FiniteCohomology
