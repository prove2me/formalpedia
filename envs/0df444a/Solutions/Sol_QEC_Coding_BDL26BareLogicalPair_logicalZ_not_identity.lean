-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.logicalZ_not_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:18:09.225369+00:00
-- url     : https://prove2.me/submissions/3e519bde-f45a-476f-a92b-e32a68d32fe8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_partnerWord_ne_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : ¬ BinaryUpToSign (logicalZ S m) binaryOne := by
  intro h
  have hz := congrArg SymplecticVector.zPart h
  exact partnerWord_ne_zero S m hz
end QEC.Coding.BDL26BareLogicalPair
