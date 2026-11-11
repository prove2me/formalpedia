-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.logical_not_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:40:12.607241+00:00
-- url     : https://prove2.me/submissions/166b8b63-4c37-4d4a-b160-2103742dabd7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logical_pairing_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : ¬ Commutes (logicalX S m) (logicalZ S m) := by
  change symplecticForm (logicalX S m).vector (logicalZ S m).vector ≠ 0
  rw [logical_pairing_one]
  exact one_ne_zero
end QEC.Coding.BDL26BareLogicalPair
