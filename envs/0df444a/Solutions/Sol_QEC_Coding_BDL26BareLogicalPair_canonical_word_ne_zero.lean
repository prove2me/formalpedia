-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.canonical_word_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:47:07.667752+00:00
-- url     : https://prove2.me/submissions/01371c87-cda0-4908-ab30-dda44ee6e01b

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
theorem _root_.solution : (canonicalGenerator S m).val ≠ 0 := by
  intro h
  have he : canonicalGenerator S m = 0 := Subtype.ext h
  apply canonical_class_ne_zero S m
  rw [he, map_zero]
end QEC.Coding.BDL26BareLogicalPair
