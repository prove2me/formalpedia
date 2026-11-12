-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.indexed_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:32:14.645722+00:00
-- url     : https://prove2.me/submissions/8ee13553-9c16-48c9-b5ef-94999d340676

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    indexedLogicalEquiv S depth i ((indexedLogicalEquiv S depth i).symm c) = c :=
  (indexedLogicalEquiv S depth i).apply_symm_apply c
end QEC.Coding.BDL26LogicalQubitPreservation
