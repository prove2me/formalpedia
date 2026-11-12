-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.indexed_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:31:45.580057+00:00
-- url     : https://prove2.me/submissions/05528bf6-7aaf-4770-b5ea-d28ee781f036

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
theorem _root_.solution (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : ((indexedFamily S depth).complex i).pureXLogicalQuotient) :
    (indexedLogicalEquiv S depth i).symm (indexedLogicalEquiv S depth i w) = w :=
  (indexedLogicalEquiv S depth i).symm_apply_apply w
end QEC.Coding.BDL26LogicalQubitPreservation
