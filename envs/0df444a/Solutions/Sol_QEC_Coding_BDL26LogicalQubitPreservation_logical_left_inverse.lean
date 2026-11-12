-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logical_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:29:25.612469+00:00
-- url     : https://prove2.me/submissions/590c6849-d0c8-462d-992e-ac42675c6a13

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
theorem _root_.solution (S : OddScale) (n : Nat) (v : LogicalQuotient S n) :
    (logicalEquiv S n).symm (logicalEquiv S n v) = v :=
  (logicalEquiv S n).symm_apply_apply v
end QEC.Coding.BDL26LogicalQubitPreservation
