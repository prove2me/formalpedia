-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.actual_code_action_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:19:53.518132+00:00
-- url     : https://prove2.me/submissions/8e9b67a5-3aca-422a-b895-2e78a5bd9cbc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_codeVector_mem
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_codeVector_ne_zero
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_preserves_code
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Zbar_preserves_code
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_action_ne_zero
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Zbar_action_ne_zero
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_product_preserves_code
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
theorem _root_.solution : ∃ ψ : Qubit.QubitRegister (Physical S m),
    ψ ∈ (labelledCode S m).carrier ∧ ψ ≠ 0 ∧
    Xbar S m ψ ∈ (labelledCode S m).carrier ∧ Zbar S m ψ ∈ (labelledCode S m).carrier ∧
    (Xbar S m * Zbar S m) ψ ∈ (labelledCode S m).carrier ∧
    Xbar S m ψ ≠ 0 ∧ Zbar S m ψ ≠ 0 ∧ (Xbar S m * Zbar S m) ψ ≠ 0 ∧
    (Xbar S m * Zbar S m - Zbar S m * Xbar S m) ψ ≠ 0 :=
  ⟨codeVector S m, codeVector_mem S m, codeVector_ne_zero S m,
    Xbar_preserves_code S m _ (codeVector_mem S m), Zbar_preserves_code S m _ (codeVector_mem S m),
    product_preserves_code S m _ (codeVector_mem S m),
    Xbar_action_ne_zero S m _ (codeVector_ne_zero S m), Zbar_action_ne_zero S m _ (codeVector_ne_zero S m),
    product_action_ne_zero S m _ (codeVector_ne_zero S m),
    commutator_action_ne_zero S m _ (codeVector_ne_zero S m)⟩
end QEC.Coding.BDL26BareLogicalPair
