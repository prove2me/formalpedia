-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.oddEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:52:47.940823+00:00
-- url     : https://prove2.me/submissions/960c256a-42bb-46eb-92f3-94f803e97e3e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_nextEquiv_mk

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
    oddEquiv S k (classOf (state S (2 * k + 1)).presentation v) =
      classOf (state S (2 * k + 2)).presentation (oddCocycle S k v) :=
  nextEquiv_mk S (2 * k + 1) (state S (2 * k + 1)) (odd_lower k) v
end QEC.Coding.BDL26RZCohomology
