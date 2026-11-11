-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.logicalZ_not_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:51:17.673991+00:00
-- url     : https://prove2.me/submissions/bb9154ea-bf11-4d28-b66b-f452e2b50a60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logical_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_comm
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_iff_of_binaryUpToSign_left


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : ¬ (stabilizer S m).InGeneratedGroupUpToSign (logicalZ S m) := by
  rintro ⟨g, hg, hv⟩
  have hzg : Commutes (logicalZ S m) (logicalX S m) :=
    (commutes_iff_of_binaryUpToSign_left hv).mpr
      ((commutes_comm g (logicalX S m)).mpr (logicalX_normalizer S m g hg))
  exact logical_not_commutes S m ((commutes_comm (logicalX S m) (logicalZ S m)).mpr hzg)
end QEC.Coding.BDL26BareLogicalPair
