-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.indexedLogicalEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:31:20.35129+00:00
-- url     : https://prove2.me/submissions/10de4f97-038e-44a1-8e77-39a9828fc525

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_mk

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : ((indexedFamily S depth).complex i).middleBoundaryCode.dual.carrier) :
    indexedLogicalEquiv S depth i
      (((indexedFamily S depth).complex i).firstCoboundaryInMiddleBoundaryDual.mkQ w) =
      BDL26FiniteCohomology.indexedEquiv S depth i
        (((indexedFamily S depth).complex i).middleCoboundaryInCocycles.mkQ
          (cocycleEquiv S i.val w)) := logicalEquiv_mk S i.val w
end QEC.Coding.BDL26LogicalQubitPreservation
