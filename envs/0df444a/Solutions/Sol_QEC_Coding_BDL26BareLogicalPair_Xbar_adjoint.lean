-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.Xbar_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:08:16.522136+00:00
-- url     : https://prove2.me/submissions/0b3ad6ad-4b9d-47fc-aa5d-138afcf1dbe7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : LinearMap.adjoint (Xbar S m) = Xbar S m :=
  adjoint_toHermitianQubitOperator_eq_self _
end QEC.Coding.BDL26BareLogicalPair
