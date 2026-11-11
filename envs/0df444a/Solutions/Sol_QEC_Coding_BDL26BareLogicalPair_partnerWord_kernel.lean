-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.partnerWord_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:21:43.1177+00:00
-- url     : https://prove2.me/submissions/7f8bf1ca-8169-4349-8fd9-a2d2f3792672

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : xSyndrome S m (partnerWord S m) = 0 :=
  (Classical.choose_spec (exists_zPartner S m)).1
end QEC.Coding.BDL26BareLogicalPair
