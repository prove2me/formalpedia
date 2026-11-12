-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logical_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:29:34.093761+00:00
-- url     : https://prove2.me/submissions/b84bbe37-7dee-415c-ae3d-66fdb8597d09

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
theorem _root_.solution (S : OddScale) (n : Nat) (c : Field) :
    logicalEquiv S n ((logicalEquiv S n).symm c) = c :=
  (logicalEquiv S n).apply_symm_apply c
end QEC.Coding.BDL26LogicalQubitPreservation
