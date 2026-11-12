-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.evenCocycle_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:48:57.993191+00:00
-- url     : https://prove2.me/submissions/cafd6084-847e-4ab7-85ca-d1980d52679c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k)).presentation) :
    (evenCocycle S k v).1 = stepMap1 S (2 * k) v.1 := rfl
end QEC.Coding.BDL26RXCohomology
