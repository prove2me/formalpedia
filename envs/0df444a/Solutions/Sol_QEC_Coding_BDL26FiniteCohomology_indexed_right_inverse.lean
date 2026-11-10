-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.indexed_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:49:17.433416+00:00
-- url     : https://prove2.me/submissions/98198c11-b392-43b6-8a4f-0e10cd7b46e0

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
theorem _root_.solution (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    indexedEquiv S depth i ((indexedEquiv S depth i).symm c) = c :=
  (indexedEquiv S depth i).apply_symm_apply c
end QEC.Coding.BDL26FiniteCohomology
