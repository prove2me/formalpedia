-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.Zbar_commutes_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:34:49.777493+00:00
-- url     : https://prove2.me/submissions/ef85b772-1179-4c15-92e3-01e45dc7bc52

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_normalizer
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_normalizer_commutes_check

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (j : Sum (ZLabel S m) (XLabel S m)) :
    Commute (Zbar S m) (toQubitOperator (check S m j)) :=
  normalizer_commutes_check S m _ (logicalZ_normalizer S m) j
end QEC.Coding.BDL26BareLogicalPair
