-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.product_action_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:02:55.180739+00:00
-- url     : https://prove2.me/submissions/849d9619-967b-4876-9663-6653fb1a1bea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_action_ne_zero
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Zbar_action_ne_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (ψ : Qubit.QubitRegister (Physical S m)) (hψ : ψ ≠ 0) :
    (Xbar S m * Zbar S m) ψ ≠ 0 := Xbar_action_ne_zero S m _ (Zbar_action_ne_zero S m ψ hψ)
end QEC.Coding.BDL26BareLogicalPair
