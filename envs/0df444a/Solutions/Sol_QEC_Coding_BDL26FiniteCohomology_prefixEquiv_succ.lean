-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.prefixEquiv_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:33:54.565887+00:00
-- url     : https://prove2.me/submissions/3d73ecbf-dbf6-4704-a098-bee40182b23d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (n : Nat) :
    prefixEquiv S (n+1) = (prefixEquiv S n).trans (stepEquiv S n) := rfl
end QEC.Coding.BDL26FiniteCohomology
