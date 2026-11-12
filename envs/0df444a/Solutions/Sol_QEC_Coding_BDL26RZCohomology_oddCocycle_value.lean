-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.oddCocycle_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:52:24.209086+00:00
-- url     : https://prove2.me/submissions/46863551-da7d-4a45-a79c-a0e11d2f6929

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
namespace QEC.Coding.BDL26RZCohomology
theorem _root_.solution (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k + 1)).presentation) :
    (oddCocycle S k v).1 = stepMap1 S (2 * k + 1) v.1 := rfl
end QEC.Coding.BDL26RZCohomology
