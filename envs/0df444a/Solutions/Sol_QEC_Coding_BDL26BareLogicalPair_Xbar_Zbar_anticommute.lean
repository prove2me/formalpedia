-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.Xbar_Zbar_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:49:17.754194+00:00
-- url     : https://prove2.me/submissions/de009e34-5ddd-43f2-baff-eb204df915ea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logical_not_commutes
import Theorems.Thm_QEC_Coding_CSSGibbs_toHermitianQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_toHermitianQubitOperator_anticommute_of_not_commutes


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : Xbar S m * Zbar S m = -(Zbar S m * Xbar S m) :=
  StabilizerCode.LocalStabilizerHamiltonian.toHermitianQubitOperator_anticommute_of_not_commutes
    _ _ (logical_not_commutes S m)
end QEC.Coding.BDL26BareLogicalPair
