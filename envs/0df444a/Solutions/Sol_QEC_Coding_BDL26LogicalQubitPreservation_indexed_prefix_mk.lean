-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.indexed_prefix_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:32:27.402861+00:00
-- url     : https://prove2.me/submissions/7a1fa20e-e69e-4036-992f-5c2a0920bbb2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_prefix_mk

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : BDL26FiniteCohomology.Cocycle S 0) :
    indexedLogicalEquiv S depth i
      (logicalClass S i.val (prefixRepresentative S i.val w)) =
      BDL26SeedCohomology.coefficient w.1 := logicalEquiv_prefix_mk S i.val w
end QEC.Coding.BDL26LogicalQubitPreservation
