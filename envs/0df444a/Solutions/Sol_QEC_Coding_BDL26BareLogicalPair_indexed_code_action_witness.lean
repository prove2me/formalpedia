-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.indexed_code_action_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:21:21.270102+00:00
-- url     : https://prove2.me/submissions/88af720a-b67d-45fd-9a5d-dcb0c1dcbb32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_codeVector_mem
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_codeVector_ne_zero
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_product_action_ne_zero
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_commutator_action_ne_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    ∃ ψ : Qubit.QubitRegister (BDL26IndexedDecoder.FamilyQ S depth i),
      ψ ∈ (indexedLabelledCode S depth i).carrier ∧ ψ ≠ 0 ∧
      (toHermitianQubitOperator (indexedLogicalX S depth i) *
        toHermitianQubitOperator (indexedLogicalZ S depth i)) ψ ≠ 0 ∧
      (toHermitianQubitOperator (indexedLogicalX S depth i) * toHermitianQubitOperator (indexedLogicalZ S depth i) -
        toHermitianQubitOperator (indexedLogicalZ S depth i) * toHermitianQubitOperator (indexedLogicalX S depth i)) ψ ≠ 0 :=
  ⟨codeVector S i.val, codeVector_mem S i.val, codeVector_ne_zero S i.val,
    product_action_ne_zero S i.val _ (codeVector_ne_zero S i.val),
    commutator_action_ne_zero S i.val _ (codeVector_ne_zero S i.val)⟩
end QEC.Coding.BDL26BareLogicalPair
