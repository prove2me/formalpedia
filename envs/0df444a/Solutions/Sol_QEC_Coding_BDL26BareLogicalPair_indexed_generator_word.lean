-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.indexed_generator_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:20:44.267345+00:00
-- url     : https://prove2.me/submissions/25b205a2-9f8d-472f-99d6-bbc8c9846340

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
theorem _root_.solution (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    (indexedLogicalX S depth i).vector.xPart = (BDL26FiniteCohomology.generator S i.val (1 : ZMod 2)).val := rfl
end QEC.Coding.BDL26BareLogicalPair
