-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.oddEquiv_symm_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:53:06.54191+00:00
-- url     : https://prove2.me/submissions/f15bbe6b-f6a3-45b5-b65c-62ecf937f867

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_nextEquiv_symm_mk
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
namespace QEC.Coding.BDL26RZCohomology
theorem _root_.solution (S : OddScale) (k : Nat)
    (w : Cocycle (state S (2 * k + 2)).presentation) :
    (oddEquiv S k).symm (classOf (state S (2 * k + 2)).presentation w) =
      classOf (state S (2 * k + 1)).presentation (oddBackwardCocycle S k w) :=
  nextEquiv_symm_mk S (2 * k + 1) (state S (2 * k + 1)) (odd_lower k) w
end QEC.Coding.BDL26RZCohomology
