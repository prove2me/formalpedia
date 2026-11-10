-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logicalToH1_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:34:10.770079+00:00
-- url     : https://prove2.me/submissions/59693776-13f6-4ed4-ab85-d699c139bc04

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalToH1 S n (logicalClass S n w) =
      BDL26FiniteCohomology.classOf S n (cocycleEquiv S n w) :=
  (complex S n).pureXLogicalQuotientEquivMiddleCohomology_mk w
end QEC.Coding.BDL26LogicalQubitPreservation
