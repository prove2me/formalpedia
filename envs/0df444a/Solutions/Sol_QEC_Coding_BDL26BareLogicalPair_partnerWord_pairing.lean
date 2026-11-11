-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.partnerWord_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:21:57.281816+00:00
-- url     : https://prove2.me/submissions/65ed3852-abd2-4be1-873a-6d427e32475e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : wordPairing (canonicalGenerator S m).val (partnerWord S m) = 1 :=
  (Classical.choose_spec (exists_zPartner S m)).2
end QEC.Coding.BDL26BareLogicalPair
