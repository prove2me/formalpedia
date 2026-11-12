-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.evenEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:49:10.157093+00:00
-- url     : https://prove2.me/submissions/b9ef1983-2014-42c8-ac0b-9def0bf5223a

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
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (S : OddScale) (k : Nat)
    (v : Cocycle (state S (2 * k)).presentation) :
    evenEquiv S k (classOf (state S (2 * k)).presentation v) =
      classOf (state S (2 * k + 1)).presentation (evenCocycle S k v) :=
  nextEquiv_mk S (2 * k) (state S (2 * k)) (even_lower k) v
end QEC.Coding.BDL26RXCohomology
