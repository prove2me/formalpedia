-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.indexed_step_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:33:04.330121+00:00
-- url     : https://prove2.me/submissions/c9846ce4-73d3-40ff-a481-00437bc44fa4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalStepEquiv_mk

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleBoundaryCode.dual.carrier) :
    indexedLogicalStepEquiv S depth i (logicalClass S i.val w) =
      logicalClass S (i.val+1) (stepRepresentative S i.val w) :=
  logicalStepEquiv_mk S i.val w
end QEC.Coding.BDL26LogicalQubitPreservation
