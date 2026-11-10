-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:41:59.442702+00:00
-- url     : https://prove2.me/submissions/ec0207d9-705f-4f34-8494-96da1d3f8f4d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalToH1_mk

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalEquiv S n (logicalClass S n w) =
      BDL26FiniteCohomology.finiteH1Equiv S n
        (BDL26FiniteCohomology.classOf S n (cocycleEquiv S n w)) := by
  change BDL26FiniteCohomology.finiteH1Equiv S n
    (logicalToH1 S n (logicalClass S n w)) = _
  rw [logicalToH1_mk]
end QEC.Coding.BDL26LogicalQubitPreservation
