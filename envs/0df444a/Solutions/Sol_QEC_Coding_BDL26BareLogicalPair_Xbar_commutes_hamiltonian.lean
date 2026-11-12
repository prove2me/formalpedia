-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.Xbar_commutes_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:18:27.984201+00:00
-- url     : https://prove2.me/submissions/0eda5624-bd66-48c0-ae47-e82f600e6181

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_commutes_check

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : Commute (Xbar S m) (hamiltonian S m) := by
  unfold hamiltonian
  apply Commute.neg_right
  exact Commute.sum_right Finset.univ
    (fun j : Sum (ZLabel S m) (XLabel S m) => toQubitOperator (check S m j))
    (Xbar S m) (fun j _ => Xbar_commutes_check S m j)
end QEC.Coding.BDL26BareLogicalPair
