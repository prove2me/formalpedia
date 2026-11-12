-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.indexed_symm_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:32:41.963205+00:00
-- url     : https://prove2.me/submissions/b8bb4ea4-3335-43bd-b3d5-8077786c626e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_symm_scalar
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    (indexedLogicalEquiv S depth i).symm c = logicalClass S i.val
      (prefixRepresentative S i.val (c • BDL26SeedCohomology.seedElement)) :=
  logicalEquiv_symm_scalar S i.val c
end QEC.Coding.BDL26LogicalQubitPreservation
