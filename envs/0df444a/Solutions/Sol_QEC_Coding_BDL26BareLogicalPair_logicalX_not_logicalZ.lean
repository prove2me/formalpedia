-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.logicalX_not_logicalZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:18:24.72434+00:00
-- url     : https://prove2.me/submissions/675599b2-a384-4a16-8ea2-164078608b0d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_canonical_word_ne_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : ¬ BinaryUpToSign (logicalX S m) (logicalZ S m) := by
  intro h
  have hx := congrArg SymplecticVector.xPart h
  exact canonical_word_ne_zero S m hx
end QEC.Coding.BDL26BareLogicalPair
