-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.indexed_step_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:33:18.650772+00:00
-- url     : https://prove2.me/submissions/3efb70df-cd9a-4678-8d4e-0b5e39e7f2b0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_stepRepresentative_word
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleBoundaryCode.dual.carrier) :
    (stepRepresentative S i.val w).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 w.1 := by
  rw [selectedMap_eq]
  exact stepRepresentative_word S i.val w
end QEC.Coding.BDL26LogicalQubitPreservation
