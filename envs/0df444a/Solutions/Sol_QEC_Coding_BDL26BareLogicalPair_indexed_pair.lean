-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.indexed_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:20:47.93643+00:00
-- url     : https://prove2.me/submissions/a61fe016-cbf7-465d-9a38-e57341addab5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_normalizer
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_not_generated
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_Zbar_anticommute

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    (stabilizer S i.val).InBinaryNormalizer (indexedLogicalX S depth i) ∧
    (stabilizer S i.val).InBinaryNormalizer (indexedLogicalZ S depth i) ∧
    ¬ (stabilizer S i.val).InGeneratedGroupUpToSign (indexedLogicalX S depth i) ∧
    ¬ (stabilizer S i.val).InGeneratedGroupUpToSign (indexedLogicalZ S depth i) ∧
    toHermitianQubitOperator (indexedLogicalX S depth i) * toHermitianQubitOperator (indexedLogicalZ S depth i) =
      -(toHermitianQubitOperator (indexedLogicalZ S depth i) * toHermitianQubitOperator (indexedLogicalX S depth i)) :=
  ⟨logicalX_normalizer S i.val, logicalZ_normalizer S i.val,
    logicalX_not_generated S i.val, logicalZ_not_generated S i.val, Xbar_Zbar_anticommute S i.val⟩
end QEC.Coding.BDL26BareLogicalPair
