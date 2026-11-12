-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.prefixRepresentative_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:29:51.185038+00:00
-- url     : https://prove2.me/submissions/e88122fb-ca8c-4300-89a0-f7ad10513b8b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_cocycleEquiv_symm_word

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S 0) :
    (prefixRepresentative S n w).1 = BDL26AlternatingCochain.map1 S n w.1 :=
  cocycleEquiv_symm_word S n (BDL26FiniteCohomology.prefixCocycle S n w)
end QEC.Coding.BDL26LogicalQubitPreservation
