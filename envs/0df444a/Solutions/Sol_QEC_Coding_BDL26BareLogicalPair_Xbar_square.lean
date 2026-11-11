-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.Xbar_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:07:21.81483+00:00
-- url     : https://prove2.me/submissions/f0bccd1a-1279-4878-aadb-ea5a214e1955

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : Xbar S m * Xbar S m = 1 := toHermitianQubitOperator_square _
end QEC.Coding.BDL26BareLogicalPair
