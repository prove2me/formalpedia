-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.commutator_action_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:46:15.985528+00:00
-- url     : https://prove2.me/submissions/8ec0491a-b58b-4406-954f-ee4a2909288c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_product_action_ne_zero
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_commutator_action

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (ψ : Qubit.QubitRegister (Physical S m)) (hψ : ψ ≠ 0) :
    (Xbar S m * Zbar S m - Zbar S m * Xbar S m) ψ ≠ 0 := by
  rw [commutator_action]
  exact smul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (product_action_ne_zero S m ψ hψ)
end QEC.Coding.BDL26BareLogicalPair
